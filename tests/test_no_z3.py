"""Lean and generation run with Z3 unavailable; never silently skip checking."""
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class NoZ3Tests(unittest.TestCase):
    def test_lean_and_C_generation_do_not_import_a_solver(self):
        # This independent process forbids even transitive imports. The CI base
        # installation additionally proves that the package is actually absent.
        program = '''
import importlib.abc,sys,json
from pathlib import Path
class Block(importlib.abc.MetaPathFinder):
 def find_spec(self,fullname,path=None,target=None):
  if fullname.split('.')[0]=='z3': raise AssertionError('Lean route imported Z3')
sys.meta_path.insert(0,Block())
from formal_spec_agent import lean_backend as gate
from protocol_lab.ir import load,Machine
from protocol_lab.codegen import render
root=Path(sys.argv[1]); task=root/'task.json'
source,goals,inputs=gate.prepare(task,root,gate.sha(task))
assert goals and source
m=load(root/'model.json'); assert render(m).startswith('#define STRING_COUNT')
Machine(m)
assert 'z3' not in sys.modules
print(json.dumps(dict(goals=len(goals),solver_imported=False)))
'''
        for example in ['lean-bytes', 'lean-c-read', 'lean-state', 'lean-efsm', 'lean-values', 'lean-machine']:
            p = subprocess.run([sys.executable, '-c', program, str(ROOT/'examples'/example)], capture_output=True, text=True, timeout=15)
            self.assertEqual(p.returncode, 0, p.stderr)
            self.assertFalse(json.loads(p.stdout)['solver_imported'])

    def test_base_environment_and_explicit_historical_solver_rejection(self):
        if os.environ.get('FSA_Z3_ABSENT_REQUIRED') == '1':
            self.assertIsNone(importlib.util.find_spec('z3'), 'Lean installation must not contain Z3')
        from protocol_lab.pipeline.runner import run
        from protocol_lab.pipeline.task import sha
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            mail = ROOT/'examples/mailbox'
            historical = json.loads((mail/'task.json').read_text())
            historical.update(schema='spec-flow-task-v2',
                              formal=dict(depth=1, symbolic_initials=[]))
            task = root/'historical.json'
            task.write_text(json.dumps(historical))
            output = root/'flow'
            with self.assertRaisesRegex(ValueError, 'Historical solver task'):
                run(task, root, output, sha(task))
            self.assertFalse(output.exists())
