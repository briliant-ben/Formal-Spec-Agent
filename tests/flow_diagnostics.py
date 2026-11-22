"""Retain original end-to-end test output before TemporaryDirectory cleanup."""
import json
import os
from pathlib import Path
import shutil


def record_flow(output, name, result):
    destination = os.environ.get('FSA_FLOW_EVIDENCE_OUT')
    if destination:
        root = Path(destination)/name
        root.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(output, root)
    return json.dumps({stage: row for stage, row in result.get('stages', {}).items()
                       if row.get('status') != 'pass'}, ensure_ascii=False)
