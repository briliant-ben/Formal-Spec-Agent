"""Stable CLI; no protocol rules or provider calls hidden in validation."""
import sys


def main():
    if len(sys.argv)>1 and sys.argv[1]=='lean-types':
        from .lean_typed import type_main
        return type_main(sys.argv[2:])
    if len(sys.argv)>1 and sys.argv[1]=='lean-native':
        from .lean_native import main as native
        return native(sys.argv[2:])
    if len(sys.argv) > 1 and sys.argv[1] in ('lean-plan', 'lean-check', 'lean-verify'):
        from .lean_backend import main as check, verify_main, plan_main
        return {'lean-plan':plan_main, 'lean-check':check, 'lean-verify':verify_main}[sys.argv[1]](sys.argv[2:])
    if len(sys.argv) > 1 and sys.argv[1] == 'propose':
        from .proposals import main as propose
        return propose(sys.argv[2:])
    from protocol_lab.pipeline.__main__ import main as pipeline
    return pipeline()


if __name__ == '__main__':
    raise SystemExit(main())
