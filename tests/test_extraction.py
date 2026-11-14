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
        self.assertEqual(evolution['schema'],'framework-source-evolution-v1')
        changes=evolution['files']
        self.assertEqual(set(changes),{'protocol_lab/codegen/__init__.py','protocol_lab/codegen/execute.py'})
        for row in manifest['files']:
            actual=hashlib.sha256((ROOT/row['target']).read_bytes()).hexdigest()
            if row['target'] in changes:
                update=changes[row['target']]
                self.assertEqual(update['extracted_sha256'],row['extracted_sha256'])
                self.assertEqual(actual,update['current_sha256'],row['target'])
                self.assertEqual(update['change'],'compact-c-generation-v5')
            else:self.assertEqual(actual,row['extracted_sha256'],row['target'])
            if row['transformation']=='none':self.assertEqual(row['extracted_sha256'],row['source_sha256'])
        self.assertFalse((ROOT/'model/tcp.json').exists())
        self.assertFalse((ROOT/'protocol_lab/packets.py').exists())
