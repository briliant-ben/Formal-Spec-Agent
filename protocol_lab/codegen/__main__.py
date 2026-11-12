"""Framework-neutral generation stage: JSON result, native C source, no LLM client."""
import argparse
import json
from pathlib import Path
from . import generate,Unsupported
from ..ir import ModelError

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('model',type=Path);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--wire-binding',type=Path)
    a=p.parse_args()
    try:r=generate(a.model,a.out,a.wire_binding)
    except (ModelError,Unsupported,ValueError,OSError)as e:
        print(json.dumps(dict(schema='spec-flow-stage-v1',stage='generate',status='rejected',
                             classification='unsupported_semantics'if isinstance(e,Unsupported)else'invalid_input',reason=str(e))))
        return 2
    print(json.dumps(r));return 0

if __name__=='__main__':raise SystemExit(main())
