"""Stable CLI; no protocol rules or provider calls hidden in validation."""
import sys


def main():
    if len(sys.argv) > 1 and sys.argv[1] == 'propose':
        from .proposals import main as propose
        return propose(sys.argv[2:])
    from protocol_lab.pipeline.__main__ import main as pipeline
    return pipeline()


if __name__ == '__main__':
    raise SystemExit(main())
