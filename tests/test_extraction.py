import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ExtractionTests(unittest.TestCase):
    def test_named_source_extraction_is_exact_or_explicitly_transformed(self):
        manifest=json.loads((ROOT/'provenance/extraction.json').read_text())
        self.assertEqual(manifest['source_commit'],'e91436f0bccc34be63c089a0c8d5584155fdf462')
        evolution=json.loads((ROOT/'provenance/evolution.json').read_text())
        self.assertEqual(evolution['schema'],'framework-source-evolution-v2')
        changes=evolution['files']
        categories={n:'native-counted-text-v6' for n in ['protocol_lab/codegen/__init__.py','protocol_lab/codegen/execute.py','protocol_lab/codegen/harness.c']}
        categories.update({n:'lean-timed-flow-v8' for n in ['protocol_lab/pipeline/task.py','protocol_lab/pipeline/worker.py','protocol_lab/pipeline/runner.py']})
        categories.update({n:'native-counted-text-v6+typed-observation-v1+model-identity' for n in ['protocol_lab/codegen/__init__.py','protocol_lab/codegen/execute.py']})
        categories['protocol_lab/pipeline/worker.py']='lean-timed-flow-v8'
        categories['protocol_lab/flow.py']='typed-observation-v1'
        categories['tests/test_rational_clock.py']='rational-reference-and-lean-scope'
        self.assertEqual(set(changes),set(categories))
        retired = evolution['retired']
        self.assertEqual(set(retired), {row['target'] for row in manifest['files']
                                         if not (ROOT/row['target']).is_file()})
        for row in manifest['files']:
            if row['transformation']=='none':
                self.assertEqual(row['extracted_sha256'],row['source_sha256'])
            if row['target'] in retired:
                entry = retired[row['target']]
                self.assertEqual(entry['extracted_sha256'],row['extracted_sha256'])
                self.assertEqual(entry['historical_commit'],'c5ef8e35fa2ed78c824a54911ec758c7d7782054')
                continue
            actual=hashlib.sha256((ROOT/row['target']).read_bytes()).hexdigest()
            if row['target'] in changes:
                update=changes[row['target']]
                self.assertEqual(update['extracted_sha256'],row['extracted_sha256'])
                self.assertEqual(actual,update['current_sha256'],row['target'])
                self.assertEqual(update['change'],categories[row['target']])
            else:self.assertEqual(actual,row['extracted_sha256'],row['target'])
        self.assertFalse((ROOT/'model/tcp.json').exists())
        self.assertFalse((ROOT/'protocol_lab/packets.py').exists())
