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
        for example in ['lean-bytes', 'lean-c-read', 'lean-state', 'lean-efsm', 'lean-values']:
            p = subprocess.run([sys.executable, '-c', program, str(ROOT/'examples'/example)], capture_output=True, text=True, timeout=15)
            self.assertEqual(p.returncode, 0, p.stderr)
            self.assertFalse(json.loads(p.stdout)['solver_imported'])

    def test_base_environment_and_explicit_missing_Z3_failure(self):
        if os.environ.get('FSA_Z3_ABSENT_REQUIRED') == '1':
            self.assertIsNone(importlib.util.find_spec('z3'), 'Lean-only installation must not contain Z3')
            with tempfile.TemporaryDirectory() as tmp:
                # Real public CLI, not an import mock: the independent native
                # stages remain runnable but the requested Z3 stage must block.
                from protocol_lab.pipeline.task import sha
                task = ROOT/'examples/mailbox/task.json'; output = Path(tmp)/'flow'
                p = subprocess.run([sys.executable,'-m','formal_spec_agent','run',str(task),'--workspace',str(task.parent),'--task-sha256',sha(task),'--out',str(output)],capture_output=True,text=True,timeout=60,cwd='/tmp')
                self.assertEqual(p.returncode,1,p.stderr)
                report = json.loads((output/'flow.json').read_text())
                self.assertEqual(report['assessment'],'blocked')
                self.assertEqual(report['stages']['formal']['classification'],'environment')
                self.assertEqual(report['stages']['formal']['status'],'blocked')
                self.assertEqual(report['stages']['compare']['status'],'pass')
                self.assertFalse(report['protocol_correctness_proved'])
        program = '''
import sys,importlib.abc
from pathlib import Path
class Block(importlib.abc.MetaPathFinder):
 def find_spec(self,fullname,path=None,target=None):
  if fullname.split('.')[0]=='z3':raise ModuleNotFoundError('deliberately absent z3')
sys.meta_path.insert(0,Block())
from protocol_lab.ir import load,ModelError
from protocol_lab.symbolic import Encoding
try: Encoding(load(Path(sys.argv[1])),1,[])
except ModelError as e:
 assert 'Z3 is missing' in str(e),str(e)
 print('explicit missing-solver rejection; no fallback or proof')
else:raise AssertionError('missing solver silently accepted')
'''
        p = subprocess.run([sys.executable, '-c', program, str(ROOT/'examples/mailbox/model.json')], capture_output=True, text=True, timeout=15)
        self.assertEqual(p.returncode, 0, p.stderr)
        self.assertIn('no fallback', p.stdout)
