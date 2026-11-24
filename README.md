# Formal-Spec-Agent

A reusable specification modeling and validation framework, with an executable
core and optional independent model-proposal roles.

```text
Pinned specification and scope → Protocol IR → reference execution / Lean contracts
  → generated tests → standalone generated C → execution observations
  → Difference and specification traceability
```

Protocol behavior belongs in declarative IR. Model providers, MCP, Skills and
external multi-agent harnesses are interchangeable callers; their self-reports
never replace acceptance. This is not yet an autonomous system that turns any
English specification into a complete, proven implementation.

[TCPIP-Model](https://github.com/briliant-ben/TCPIP-Model) is the IPv4 case study:
it owns TCP/IP models, RFC bindings, independent oracles, PCAP and Linux/lwIP
adapters. This repository owns the evolving generic semantics and runtime.
[Extraction provenance](provenance/extraction.json) records each original blob
and the explicitly transformed boundaries.

## Repository map

| Directory | Role |
|---|---|
| `formal_spec_agent/` | Public CLI, optional independent proposal roles and provider adapters |
| `protocol_lab/` | Generic IR, reference interpreter, C lowering/runtime and ten-stage pipeline |
| `examples/mailbox/` | Small non-network specification, IR, independent literal seed and task |
| `examples/lean-timed-efsm/` | Timed EFSM benchmark (`TimedProof.lean` + ten-stage verified C99 flow) |
| `tests/` | Semantic, execution, concurrency, tamper and rejection checks |
| `docs/` | [IR overview](docs/ir-semantics.md), [parallel-agent workflow](docs/parallel-agents.md), [role contract](docs/agent-contract.md), [extraction boundary](docs/extraction.md) |
| `provenance/`, `evidence/` | Source origin and retained validation/review records |

The internal package name `protocol_lab` is retained to avoid gratuitous semantic
changes during extraction. It is framework code, not a copied protocol stack.

## Install and run without a model provider

The primary Lean example now runs the complete flow without Z3:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -e .
export FSA_LEAN=/path/to/lean-4.35.0/bin/lean
TASK_SHA=$(shasum -a 256 examples/lean-efsm/flow.json | cut -d ' ' -f 1)
.venv/bin/formal-spec-agent run examples/lean-efsm/flow.json \
  --workspace examples/lean-efsm --task-sha256 "$TASK_SHA" --out /tmp/lean-flow-001
.venv/bin/formal-spec-agent verify /tmp/lean-flow-001 \
  --workspace examples/lean-efsm --task-sha256 "$TASK_SHA"
```

The [two-state example](examples/lean-efsm/README.md) checks all declared rules
for its timer-free integer fragment. It is not a full TCP/IP or compiler proof.
Install official Lean separately. [Task-v6 and proof boundaries](docs/lean-efsm-flow.md)
describe universal obligations, snapshots, explicit failures and fresh rechecking.

Requirements are Python 3.11+, a POSIX host, a C99 compiler and Lean 4.35.0
for formal checks. Install with `pip install .`. Python package dependencies
are empty. See [Lean migration and supported fragments](docs/lean-first.md).

The example is a **finite byte mailbox**, not an Internet protocol. Its source,
literal seed, Lean proof and finite exploration domain are pinned before execution. Use a
fresh output directory outside the tool tree:

```sh
TASK_SHA=$(shasum -a 256 examples/mailbox/task.json | cut -d ' ' -f 1)
.venv/bin/formal-spec-agent run examples/mailbox/task.json \
  --workspace examples/mailbox --task-sha256 "$TASK_SHA" --out /tmp/mailbox-run-001
.venv/bin/formal-spec-agent verify /tmp/mailbox-run-001 \
  --workspace examples/mailbox --task-sha256 "$TASK_SHA"
```

A locally calculated digest binds a version; independent approval must come from
the acceptance controller. Exit0 means the declared slice passed, exit1 includes
unresolved/failed execution, and exit2 rejects input/evidence. Unsupported
semantics and UNKNOWN must be explicit. Tests, rule coverage and bounded checks
do not imply full specification or compiler correctness.

External protocol data stays in its own workspace:

```sh
.venv/bin/formal-spec-agent run /path/to/your-protocol/task.json \
  --workspace /path/to/your-protocol --task-sha256 APPROVED_TASK_SHA --out /tmp/tcp-framework-001
```

The TCPIP-Model repository is now a small model/C/demo snapshot, without the old
`flows/` tree or a framework submodule. Its optional `code/regenerate.py` uses an
external pinned framework checkout. Complete historical TCP/UDP tasks remain at
the Git versions named in the extraction evidence; the command above expects a
caller-supplied, independently approved workspace/task.

[C generation](docs/c-code-generation.md) shares repeated expressions and emits
readable string literals while retaining strict traces and failure checks.

Protocol byte layout should be expressed in IR. The old TCP-specific `wire` codec
was not extracted into the generic backend: requesting it is explicitly rejected.
Existing TCP network channels are reproduced in the benchmark repository.

## Lean-first proof backend

The [Lean expression pilot](docs/lean-proof-gates.md) adds kernel-checked
contracts for a selected pure IR byte expression. It uses frozen definitions,
restricted proof data, explicit positive witnesses and a separate axiom audit.
The [byte example](examples/lean-bytes/README.md) includes DeepSeek-proposed
proof data which still must pass actual Lean checking. Lean 4.35.0 is pinned.
Historical solver tasks can be reproduced using their original pinned Git
revision. Current tasks use the Lean formal stage.
Their old results are not relabeled as Lean proofs.

`formal-spec-agent lean-plan` drafts statements for independent approval;
`lean-check` checks all frozen obligations; `lean-verify` reconstructs a fresh
project and checks again. A passing expression certificate is neither a C
compiler proof nor full-model/protocol verification. The dedicated Lean CI
requires the real checker and exercises both successful and rejected proofs.

The [C correspondence unit](docs/code-generation-paths.md) independently parses
an actual generated C assignment, reifies its typed expression and checks it
against formal IR lowering. It includes an optional `lean-native` route that
compiles the IR reference through Lean to C and runs frozen witnesses, requiring
Lean's runtime. Neither route implies native compiler or whole-protocol correctness.

The [state transaction unit](examples/lean-state/README.md) derives ordered integer
assignments, buffered emissions and final-invariant rollback from an IR action
block. Its separate `checked_state_contract` result does not certify C statements,
guard selection, timers or a complete EFSM. See [supported fragments](docs/lean-first.md)
for the active Lean-only scopes and open compiler-correspondence work.

The [typed value layer](docs/lean-typed-values.md) now covers all five types and
26 operators of the pinned compact TCP/IP model. Its entire expression view can
be typechecked, with explicit source bindings; this is distinct from proving the
335-rule EFSM safe. A separate 59-obligation benchmark and compiled Lean reference
exercise exact values, long buffers, wrap, checksum and Unicode/NUL. Typed
transition and scheduler properties are treated in the timed contracts.

The [scheduled microstep layer](docs/lean-scheduled-microsteps.md) now derives
all compact-case actions, unique guard selection, typed updates/messages and
individual timer firings. A separate29-obligation kernel contract covers ordered
effects, conflicts and rollback; compiled Lean matches18 benchmark operations and
nine unchanged TCPIP transitions. Batch dispatch and all-rule typed preservation
are checked in the timed endpoint proof.

The [timed replay certificate](examples/lean-timed-efsm/README.md) uses the
public Lean checker to prove exact finite dispatch and tick results, including
timer order, emitted data and an explicit rollback snapshot on failure.
The [timed contracts](docs/lean-timed-contracts.md) track the separate
universal scheduler and model obligations.

## Scaling protocols with `compose` & `campaign`

For multi-component protocols whose rule/proof count exceeds single-prompt
context limits and single-module Lean elaboration budgets, `compose` merges
hash-pinned IR components (with optional namespace prefixes) into a validated IR
model, and `campaign` precompiles core `.olean`s once, decomposes `Approved` into
independent `core_contracts`, `conflict_shard_NNN`, and `firing_shard_NNN` units
under POSIX locks, runs parallel workers (`claim`/`submit` for any external agent
harness or `run-workers --backend command|provider`), caches verified shards by
input digest, and assembles `TimedProof.lean` + standalone C99 via the ten-stage
pipeline. See [the parallel-agent workflow guide](docs/parallel-agents.md) and
the generic timed benchmark in [examples/lean-timed-efsm](examples/lean-timed-efsm/README.md).

## Optional independent proposal roles

`formal-spec-agent propose` executes one to four independent JSON roles with
pinned specification/job inputs and the original shared request ledger. Included
provider adapters support Gemini (`--provider gemini`, default) and DeepSeek
(`--provider deepseek`); the operator supplies a model name.
The controller does not execute model-returned code, edit models/oracles, retry
failed paid requests or let a role approve its own protocol.

```sh
.venv/bin/formal-spec-agent propose --job /candidate/job.json --workspace /candidate \
  --job-sha256 APPROVED_JOB_SHA --out /runs/proposal-001 \
  --ledger /private/shared-ledger --credential-file /private/gemini.key \
  --provider gemini --model gemini-2.5-flash
```

`requires_controller_review` means proposals were received, not accepted. A trusted
controller must review them and invoke `run`/`verify`. Credentials, ledger and
outputs must be outside the candidate workspace. Calls are capped by default;
explicitly authorized operators may use `--uncapped-calls` without resetting the
ledger. See [the role/trust contract](docs/agent-contract.md). Tests use a fake
provider and incur no API fees.

The [milestone roadmap](docs/roadmap.md) separates the implemented Lean unit
from future implementation correspondence and persistent agent orchestration.

## Scope and historical contracts

Each protocol still needs its own specification version, scope, assumptions,
IR and independent acceptance conditions. C buffer/number limits, bounded depth
and trusted components do not expand because code moved into a new repository.
[The extraction boundary](docs/extraction.md) distinguishes active maintenance,
frozen old checkers and new evidence epochs. Protocol models, private credentials,
venvs and compiled binaries are not migrated here.

Current guides are English. The imported `docs/semantics.md` remains a historical
source contract at its hash-pinned original bytes/language; the
[English semantics overview](docs/ir-semantics.md) is its reader-facing entry.

The [typed batch scheduler](docs/lean-batch-scheduling.md) now has checked generic
termination/replay lemmas and a compiled input-only reference. Its 57-obligation literal
certificate checks and freshly rechecks against the pinned Lean semantics.

The [universal typed EFSM gate](docs/lean-typed-efsm.md) now checks raw
preservation, guard disjointness and coverage for all five IR value kinds in a
timer-free fragment. Its [Typed Cell benchmark](examples/lean-typed-efsm) has 14
kernel-checked obligations plus fresh rechecking. Universal contracts and finite
execution witnesses are reported separately. Its explicit task-v7 now runs all
ten stages without Z3, including independent C text input, generated tests,
Difference and traceability. The separate [timed endpoint proof](docs/lean-timed-contracts.md)
checks all 335 raw firings, 18 guard conflict groups and dispatch contracts of
the pinned TCP/IP model. Reachability coverage and C compiler correctness remain
separate obligations.
