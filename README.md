# Formal-Spec-Agent

A reusable specification modeling and validation framework, with an executable
core and optional independent model-proposal roles.

```text
Pinned specification and scope → Protocol IR → reference execution / independent Z3
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
| `formal_spec_agent/` | Public CLI, optional independent proposal roles and provider adapter |
| `protocol_lab/` | Generic IR, reference interpreter, Z3, C lowering/runtime and ten-stage pipeline |
| `examples/mailbox/` | Small non-network specification, IR, independent literal seed and task |
| `tests/` | Semantic, execution, concurrency, tamper and rejection checks |
| `docs/` | [IR overview](docs/ir-semantics.md), [role contract](docs/agent-contract.md), [extraction boundary](docs/extraction.md) |
| `provenance/`, `evidence/` | Source origin and retained validation/review records |

The internal package name `protocol_lab` is retained to avoid gratuitous semantic
changes during extraction. It is framework code, not a copied protocol stack.

## Install and run without a model provider

Requirements: Python3.11+, a POSIX host and a C99 compiler. Z3 is pinned. No API
key, network privilege or existing network stack is needed for deterministic checks.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -e .
.venv/bin/python -m unittest discover -s tests -v
```

The example is a **finite byte mailbox**, not an Internet protocol. Its source,
literal seed and finite exploration domain are pinned before execution. Use a
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
.venv/bin/formal-spec-agent run /path/to/TCPIP-Model/flows/tcp-active-open.json \
  --workspace /path/to/TCPIP-Model --task-sha256 APPROVED_TASK_SHA --out /tmp/tcp-framework-001
```

[C generation](docs/c-code-generation.md) shares repeated expressions and emits
readable string literals while retaining strict traces and failure checks.

Protocol byte layout should be expressed in IR. The old TCP-specific `wire` codec
was not extracted into the generic backend: requesting it is explicitly rejected.
Existing TCP network channels are reproduced in the benchmark repository.

## Optional independent proposal roles

`formal-spec-agent propose` executes one to four independent JSON roles with
pinned specification/job inputs and the original shared request ledger. The
included provider adapter supports DeepSeek; the operator supplies a model name.
The controller does not execute model-returned code, edit models/oracles, retry
failed paid requests or let a role approve its own protocol.

```sh
.venv/bin/formal-spec-agent propose --job /candidate/job.json --workspace /candidate \
  --job-sha256 APPROVED_JOB_SHA --out /runs/proposal-001 \
  --ledger /private/shared-ledger --credential-file /private/deepseek.key --model YOUR_MODEL
```

`requires_controller_review` means proposals were received, not accepted. A trusted
controller must review them and invoke `run`/`verify`. Credentials, ledger and
outputs must be outside the candidate workspace. Calls are capped by default;
explicitly authorized operators may use `--uncapped-calls` without resetting the
ledger. See [the role/trust contract](docs/agent-contract.md). Tests use a fake
provider and incur no API fees.

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
