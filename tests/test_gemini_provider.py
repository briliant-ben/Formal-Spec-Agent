"""Offline unit tests for the bounded Gemini proposal gateway and provider selection."""
import contextlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock
import urllib.error

from formal_spec_agent import proposals
from formal_spec_agent.providers import DEFAULT_PROVIDER, PROVIDERS, get_provider
from formal_spec_agent.providers import gemini


class _FakeResponse:
    def __init__(self, payload_bytes):
        self._payload = payload_bytes

    def read(self, limit=-1):
        if limit is None or limit < 0:
            return self._payload
        return self._payload[:limit]

    def __enter__(self):
        return self

    def __exit__(self, exc_type, exc, tb):
        return False


class GeminiProviderTests(unittest.TestCase):
    def _write_secret(self, path, secret='gemini-secret-key', mode=0o600):
        path.write_text(secret + '\n')
        os.chmod(path, mode)
        return path

    def test_provider_registry_and_unknown_rejection(self):
        self.assertEqual(DEFAULT_PROVIDER, 'gemini')
        self.assertEqual(set(PROVIDERS), {'gemini', 'deepseek'})
        self.assertIs(get_provider('gemini'), gemini.request)
        with self.assertRaisesRegex(ValueError, 'Unsupported model provider'):
            get_provider('unknown-provider')

    def test_gemini_request_payload_caching_and_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            secret_file = self._write_secret(root / 'gemini.key')
            ledger = root / 'ledger'
            seen = []

            def fake_open(req, timeout=0):
                seen.append((req.full_url, dict(req.header_items()), json.loads(req.data.decode()), timeout))
                answer = {
                    'responseId': 'resp-1',
                    'modelVersion': 'gemini-2.5-flash',
                    'usageMetadata': {'promptTokenCount': 10, 'candidatesTokenCount': 5},
                    'candidates': [{
                        'finishReason': 'STOP',
                        'content': {
                            'parts': [
                                {'thought': True, 'text': 'internal thinking'},
                                {'text': '{"protocol": "demo", "accepted": true}'},
                            ]
                        },
                    }],
                }
                return _FakeResponse(json.dumps(answer).encode())

            messages = [
                {'role': 'system', 'content': 'System rule 1.'},
                {'role': 'system', 'content': 'System rule 2.'},
                {'role': 'user', 'content': 'Propose a model'},
                {'role': 'assistant', 'content': '{"draft": 1}'},
                {'role': 'user', 'content': 'Refine it'},
            ]
            with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(gemini, '_open', side_effect=fake_open):
                first = gemini.request(messages, ledger, secret_file, model='gemini-2.5-pro',
                                       max_tokens=1024, max_calls=1, thinking='enabled', reasoning_effort='high')
                cached = gemini.request(messages, ledger, secret_file, model='gemini-2.5-pro',
                                        max_tokens=1024, max_calls=1, thinking='enabled', reasoning_effort='high')
                with self.assertRaisesRegex(ValueError, 'budget'):
                    gemini.request([{'role': 'user', 'content': 'Another call'}], ledger, secret_file,
                                   model='gemini-2.5-pro', max_tokens=1024, max_calls=1)

            self.assertEqual(len(seen), 1)
            url, headers, body, _ = seen[0]
            self.assertEqual(url, 'https://generativelanguage.googleapis.com/v1beta/models/gemini-2.5-pro:generateContent')
            self.assertNotIn('gemini-secret-key', url)
            headers_lower = {k.lower(): v for k, v in headers.items()}
            self.assertEqual(headers_lower.get('x-goog-api-key'), 'gemini-secret-key')
            self.assertEqual(body['systemInstruction'], {'parts': [{'text': 'System rule 1.\n\nSystem rule 2.'}]})
            self.assertEqual([c['role'] for c in body['contents']], ['user', 'model', 'user'])
            self.assertEqual(body['generationConfig'], {
                'responseMimeType': 'application/json',
                'maxOutputTokens': 1024,
                'thinkingConfig': {'thinkingBudget': 8192},
            })
            self.assertFalse(first['cached'])
            self.assertTrue(cached['cached'])
            saved = json.loads((ledger / first['response_file']).read_text())
            self.assertEqual(saved['response'], {'protocol': 'demo', 'accepted': True})
            self.assertEqual(ledger.stat().st_mode & 0o777, 0o700)

    def test_error_conditions_and_no_auto_retry(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            secret_file = self._write_secret(root / 'gemini.key')

            # Invalid model name (path traversal)
            with self.assertRaisesRegex(ValueError, 'Invalid Gemini model name'):
                gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l1', secret_file, model='../bad')
            with self.assertRaisesRegex(ValueError, 'Invalid Gemini model name'):
                gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l1b', secret_file, model='gemini..bad')

            # Thinking disabled with reasoning_effort
            with self.assertRaisesRegex(ValueError, 'reasoning'):
                gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l2', secret_file,
                               thinking='disabled', reasoning_effort='high')

            # Prompt byte budget exceeded
            with self.assertRaisesRegex(ValueError, 'Prompt byte budget'):
                gemini.request([{'role': 'user', 'content': 'a' * 97000}], root / 'l3', secret_file)

            # Credential file permissions rejected and no HTTP call made
            bad_secret = self._write_secret(root / 'world.key', mode=0o644)
            called = []
            with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(gemini, '_open', side_effect=lambda *a, **k: called.append(1)):
                with self.assertRaisesRegex(ValueError, 'did not complete'):
                    gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l4', bad_secret)
            self.assertEqual(called, [])

            # HTTP error records failure and prevents retry
            http_calls = []

            def fail_http(req, timeout=0):
                http_calls.append(1)
                raise urllib.error.HTTPError(req.full_url, 429, 'Too Many Requests', {}, None)

            with mock.patch.dict(os.environ, {'GEMINI_API_KEY': 'env-secret'}, clear=True), \
                    mock.patch.object(gemini, '_open', side_effect=fail_http):
                with self.assertRaisesRegex(ValueError, 'did not complete'):
                    gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l5', secret_file)
                with self.assertRaisesRegex(ValueError, 'no automatic paid retry'):
                    gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l5', secret_file)
            self.assertEqual(len(http_calls), 1)
            ledger_rows = json.loads((root / 'l5/ledger.json').read_text())
            row = next(iter(ledger_rows.values()))
            self.assertEqual(row['status'], 'failed')
            self.assertEqual(row['http_status'], 429)
            self.assertNotIn('env-secret', json.dumps(ledger_rows))

            # Incomplete finishReason rejected
            def incomplete(req, timeout=0):
                body = json.dumps({'candidates': [{'finishReason': 'MAX_TOKENS', 'content': {'parts': [{'text': '{}'}]}}]}).encode()
                return _FakeResponse(body)

            with mock.patch.dict(os.environ, {'GEMINI_API_KEY': 'env-secret'}, clear=True), \
                    mock.patch.object(gemini, '_open', side_effect=incomplete):
                with self.assertRaisesRegex(ValueError, 'did not complete'):
                    gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l6', secret_file)

            # Secret appearing in response is rejected and not written
            def leak_secret(req, timeout=0):
                body = json.dumps({'candidates': [{'finishReason': 'STOP', 'content': {'parts': [{'text': '{"k": "env-secret"}'}]}}]}).encode()
                return _FakeResponse(body)

            with mock.patch.dict(os.environ, {'GEMINI_API_KEY': 'env-secret'}, clear=True), \
                    mock.patch.object(gemini, '_open', side_effect=leak_secret):
                with self.assertRaisesRegex(ValueError, 'did not complete'):
                    gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l7', secret_file)
            self.assertEqual(list((root / 'l7').glob('*.provider.json')), [])

            # Non-object JSON response rejected
            def list_json(req, timeout=0):
                body = json.dumps({'candidates': [{'finishReason': 'STOP', 'content': {'parts': [{'text': '[1, 2, 3]'}]}}]}).encode()
                return _FakeResponse(body)

            with mock.patch.dict(os.environ, {'GEMINI_API_KEY': 'env-secret'}, clear=True), \
                    mock.patch.object(gemini, '_open', side_effect=list_json):
                with self.assertRaisesRegex(ValueError, 'did not complete'):
                    gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l8', secret_file)

            # Oversized (> 2 MiB) response rejected before JSON parse
            def oversized_resp(req, timeout=0):
                return _FakeResponse(b'x' * (2 * 1024 * 1024 + 5))

            with mock.patch.dict(os.environ, {'GEMINI_API_KEY': 'env-secret'}, clear=True), \
                    mock.patch.object(gemini, '_open', side_effect=oversized_resp):
                with self.assertRaisesRegex(ValueError, 'did not complete'):
                    gemini.request([{'role': 'user', 'content': 'hi'}], root / 'l9', secret_file)
            self.assertEqual(list((root / 'l9').glob('*.provider.json')), [])

    def test_proposals_run_and_cli_support_gemini_provider(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            workspace = root / 'candidate'
            workspace.mkdir()
            spec = workspace / 'spec.md'
            spec.write_text('one rule\n')
            job_data = {
                'schema': 'formal-spec-proposal-job-v1',
                'id': 'gemini-test',
                'sources': [{'path': 'spec.md', 'sha256': proposals.sha(spec)}],
                'roles': [{'id': 'modeler', 'messages': [{'role': 'user', 'content': 'propose'}]}],
            }
            job = workspace / 'job.json'
            job.write_text(json.dumps(job_data))
            secret = self._write_secret(root / 'gemini.key')

            def fake_open(req, timeout=0):
                answer = {
                    'candidates': [{
                        'finishReason': 'STOP',
                        'content': {'parts': [{'text': '{"accepted": true, "protocol": "tiny"}'}]},
                    }],
                }
                return _FakeResponse(json.dumps(answer).encode())

            with mock.patch.dict(os.environ, {}, clear=True), mock.patch.object(gemini, '_open', side_effect=fake_open):
                out_dir = root / 'out'
                stdout = io.StringIO()
                with contextlib.redirect_stdout(stdout):
                    rc = proposals.main([
                        '--job', str(job),
                        '--workspace', str(workspace),
                        '--out', str(out_dir),
                        '--ledger', str(root / 'ledger'),
                        '--credential-file', str(secret),
                        '--job-sha256', proposals.sha(job),
                        '--provider', 'gemini',
                        '--model', 'gemini-2.5-flash',
                    ])
            self.assertEqual(rc, 0)
            result = json.loads(stdout.getvalue())
            self.assertEqual(result['provider'], 'gemini')
            self.assertEqual(result['status'], 'requires_controller_review')
            self.assertFalse(result['protocol_accepted'])
            self.assertEqual(json.loads((out_dir / 'modeler.json').read_text()), {'accepted': True, 'protocol': 'tiny'})

            with self.assertRaises(ValueError):
                proposals.run(job, workspace, root / 'out-bad', root / 'ledger', secret,
                              'bad-model', proposals.sha(job), provider_name='unknown')
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as cm:
                proposals.main([
                    '--job', str(job),
                    '--workspace', str(workspace),
                    '--out', str(root / 'out-bad-cli'),
                    '--ledger', str(root / 'ledger'),
                    '--credential-file', str(secret),
                    '--job-sha256', proposals.sha(job),
                    '--provider', 'unknown',
                    '--model', 'x',
                ])
            self.assertEqual(cm.exception.code, 2)


if __name__ == '__main__':
    unittest.main()
