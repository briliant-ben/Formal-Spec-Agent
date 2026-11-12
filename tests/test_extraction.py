import hashlib
import json
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ExtractionTests(unittest.TestCase):
    def test_named_source_extraction_is_exact_or_explicitly_transformed(self):
        manifest=json.loads((ROOT/'provenance/extraction.json').read_text())
        self.assertEqual(manifest['source_commit'],'e91436f0bccc34be63c089a0c8d5584155fdf462')
        for row in manifest['files']:
            actual=hashlib.sha256((ROOT/row['target']).read_bytes()).hexdigest()
            self.assertEqual(actual,row['extracted_sha256'],row['target'])
            if row['transformation']=='none':self.assertEqual(actual,row['source_sha256'])
        self.assertFalse((ROOT/'model/tcp.json').exists())
        self.assertFalse((ROOT/'protocol_lab/packets.py').exists())
