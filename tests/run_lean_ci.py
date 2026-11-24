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


def partition_tests(tests):
    tcpip = [t for t in tests if t.id() == HEAVY]
    campaign = [t for t in tests if t.id().startswith('test_campaign.')]
    core = [t for t in tests if t.id() != HEAVY and not t.id().startswith('test_campaign.')]
    return {'core': core, 'tcpip-timed': tcpip, 'campaign': campaign}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('partition', choices=('core', 'tcpip-timed', 'campaign'))
    args = parser.parse_args()
    tests = list(flatten(unittest.defaultTestLoader.discover(str(Path(__file__).parent))))
    buckets = partition_tests(tests)
    if len(buckets['tcpip-timed']) != 1:
        parser.error('Expected exactly one endpoint proof test in the full suite')
    if not buckets['campaign']:
        parser.error('Expected at least one campaign test in the full suite')
    if sum(len(v) for v in buckets.values()) != len(tests):
        parser.error('Disjoint CI partitions must cover every discovered test')
    selected = buckets[args.partition]
    print(f'Partition {args.partition}: {len(selected)} of {len(tests)} tests', flush=True)
    result = unittest.TextTestRunner(verbosity=2).run(unittest.TestSuite(selected))
    return 0 if result.wasSuccessful() else 1


if __name__ == '__main__':
    sys.exit(main())
