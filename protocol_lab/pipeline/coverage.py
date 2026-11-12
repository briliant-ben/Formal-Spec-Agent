"""Standalone pure coverage accounting candidates.

This module summarizes which declared rule IDs are covered by a set of
records, separating default-initial and override cases, and breaking down
coverage by origin. It performs no reachability proof.
"""


VALID_ORIGINS = frozenset({
    'model_generated',
    'declared_seed',
    'model_generated_rejection',
    'live_observation',
})

VALID_STATUSES = frozenset({'pass', 'fail', 'unknown'})


def summarize(rule_ids, records):
    """Return a coverage accounting summary.

    Args:
        rule_ids: iterable of unique declared rule ID strings.
        records: iterable of record dicts. Each record must contain:
            key: unique record identifier
            origin: one of VALID_ORIGINS
            initial_override: boolean stating whether the case used an
                initial-state override rather than the default initial state.
            status: one of 'pass', 'fail', or 'unknown'.
            transitions: list of rule ID strings, representing the
                committed prefix for failing or unknown cases (caller
                contract), or the full executed transition list for passing
                cases.

    Returns:
        dict with keys:
            'declared_rule_ids': sorted list of declared IDs
            'covered_default': sorted list of IDs covered by passing records
                with initial_override=False
            'uncovered_default': sorted list of IDs not covered by passing
                records with initial_override=False
            'covered_override': sorted list of IDs covered by passing
                records with initial_override=True
            'uncovered_override': sorted list of IDs not covered by passing
                records with initial_override=True
            'covered_overall': sorted union of covered_default and
                covered_override
            'uncovered_overall': sorted list of declared IDs not in
                covered_overall
            'covered_by_origin': dict origin -> sorted list of IDs covered
                by passing records of that origin (both default and
                override cases)
            'uncovered_by_origin': dict origin -> sorted list of declared
                IDs not covered by passing records of that origin
            'origin_summary': dict origin -> {
                'passing_records': int,
                'failing_records': int,
                'unknown_records': int,
                'covered_default': sorted list,
                'covered_override': sorted list,
            }
            'total_declared': int
            'total_covered': int
            'total_uncovered': int

    Raises:
        ValueError: if rule_ids or records are malformed.
    """
    # Validate rule_ids container: must be iterable, not str/bytes, and elements must be non-empty strings.
    if isinstance(rule_ids, (str, bytes)):
        raise ValueError("rule_ids must be an iterable of strings, not str/bytes")
    try:
        rule_ids = list(rule_ids)
    except TypeError as exc:
        raise ValueError("rule_ids must be iterable") from exc
    if not all(isinstance(r, str) and r for r in rule_ids):
        raise ValueError("rule_ids must be non-empty strings")
    if len(rule_ids) != len(set(rule_ids)):
        raise ValueError("rule_ids must be unique")

    rule_set = set(rule_ids)

    # Validate records container: must be iterable, not str/bytes.
    if isinstance(records, (str, bytes)):
        raise ValueError("records must be an iterable of record dicts, not str/bytes")
    try:
        records_iter = iter(records)
    except TypeError as exc:
        raise ValueError("records must be iterable") from exc

    seen_keys = set()
    normalized_records = []
    for idx, rec in enumerate(records_iter):
        # Ensure each record is a dict (not list, string, etc.)
        if not isinstance(rec, dict):
            raise ValueError(f"record {idx} must be a dict")
        required = {'key', 'origin', 'initial_override', 'status', 'transitions'}
        # Check exactly required keys; no extra keys allowed.
        if set(rec.keys()) != required:
            raise ValueError(
                f"record keys must be exactly {sorted(required)}; got {sorted(map(repr, rec.keys()))}"
            )
        key = rec['key']
        if not isinstance(key, str) or not key:
            raise ValueError("record key must be a non-empty string")
        if key in seen_keys:
            raise ValueError(f"duplicate record key {key!r}")
        seen_keys.add(key)

        origin = rec['origin']
        if not isinstance(origin, str):
            raise ValueError(f"record {key!r}: origin must be a string")
        if origin not in VALID_ORIGINS:
            raise ValueError(
                f"record {key!r}: origin {origin!r} not one of {sorted(VALID_ORIGINS)}"
            )

        override = rec['initial_override']
        if not isinstance(override, bool):
            raise ValueError(f"record {key!r}: initial_override must be bool")

        status = rec['status']
        if not isinstance(status, str):
            raise ValueError(f"record {key!r}: status must be a string")
        if status not in VALID_STATUSES:
            raise ValueError(
                f"record {key!r}: status {status!r} not one of {sorted(VALID_STATUSES)}"
            )

        transitions = rec['transitions']
        if not isinstance(transitions, list):
            raise ValueError(f"record {key!r}: transitions must be a list")
        if not all(isinstance(t, str) and t for t in transitions):
            raise ValueError(f"record {key!r}: transitions must be non-empty strings")
        unknown = set(transitions) - rule_set
        if unknown:
            raise ValueError(
                f"record {key!r}: unknown rule IDs {sorted(unknown)}"
            )

        normalized_records.append({
            'key': key,
            'origin': origin,
            'initial_override': override,
            'status': status,
            'transitions': list(transitions),
        })

    # Coverage from passing records only.
    # For passing records, all transitions in the list are considered covered.
    # For failing/unknown records, no coverage contribution is made,
    # even though the committed prefix may be listed; the caller is
    # responsible for providing only the committed prefix in those lists.
    covered_default = set()
    covered_override = set()
    origin_stats = {o: {
        'passing_records': 0,
        'failing_records': 0,
        'unknown_records': 0,
        'covered_default': set(),
        'covered_override': set(),
    } for o in VALID_ORIGINS}

    for rec in normalized_records:
        stats = origin_stats[rec['origin']]
        if rec['status'] == 'pass':
            stats['passing_records'] += 1
            if rec['initial_override']:
                covered_override.update(rec['transitions'])
                stats['covered_override'].update(rec['transitions'])
            else:
                covered_default.update(rec['transitions'])
                stats['covered_default'].update(rec['transitions'])
        elif rec['status'] == 'fail':
            stats['failing_records'] += 1
        else:  # unknown
            stats['unknown_records'] += 1

    covered_overall = covered_default | covered_override

    uncovered_default = rule_set - covered_default
    uncovered_override = rule_set - covered_override
    uncovered_overall = rule_set - covered_overall

    covered_by_origin = {
        o: sorted(origin_stats[o]['covered_default'] | origin_stats[o]['covered_override'])
        for o in VALID_ORIGINS
    }
    uncovered_by_origin = {
        o: sorted(rule_set - (origin_stats[o]['covered_default'] | origin_stats[o]['covered_override']))
        for o in VALID_ORIGINS
    }

    origin_summary = {
        o: {
            'passing_records': origin_stats[o]['passing_records'],
            'failing_records': origin_stats[o]['failing_records'],
            'unknown_records': origin_stats[o]['unknown_records'],
            'covered_default': sorted(origin_stats[o]['covered_default']),
            'covered_override': sorted(origin_stats[o]['covered_override']),
        }
        for o in VALID_ORIGINS
    }

    return {
        'declared_rule_ids': sorted(rule_set),
        'covered_default': sorted(covered_default),
        'uncovered_default': sorted(uncovered_default),
        'covered_override': sorted(covered_override),
        'uncovered_override': sorted(uncovered_override),
        'covered_overall': sorted(covered_overall),
        'uncovered_overall': sorted(uncovered_overall),
        'covered_by_origin': covered_by_origin,
        'uncovered_by_origin': uncovered_by_origin,
        'origin_summary': origin_summary,
        'total_declared': len(rule_set),
        'total_covered': len(covered_overall),
        'total_uncovered': len(uncovered_overall),
    }
