"""Run disjoint CI partitions without changing any test or prover budget."""
import argparse
from pathlib import Path
import sys
import unittest

HEAVY = ('test_lean_scheduled_preservation.ScheduledPreservationTests.'
         'test_pinned_tcpip_catalogs_conflict_groups_and_unwired_events')


def flatten(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from flatten(item)
        else:
            yield item


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('partition', choices=('core', 'tcpip-timed'))
    args = parser.parse_args()
    tests = list(flatten(unittest.defaultTestLoader.discover(str(Path(__file__).parent))))
    if sum(test.id() == HEAVY for test in tests) != 1:
        parser.error('Expected exactly one endpoint proof test in the full suite')
    selected = [test for test in tests if (test.id() == HEAVY) == (args.partition == 'tcpip-timed')]
    print(f'Partition {args.partition}: {len(selected)} of {len(tests)} tests', flush=True)
    result = unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(selected))
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(main())
