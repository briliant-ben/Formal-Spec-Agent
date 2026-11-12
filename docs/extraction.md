# Framework extraction, version 0.1

The extraction baseline is TCPIP-Model Git
`e91436f0bccc34be63c089a0c8d5584155fdf462`, merged by its owner in PR27.
`provenance/extraction.json` names each selected blob and digest. IR semantics,
reference interpreter, independent symbolic encoding, sequence induction,
initialized-step checks, C lowering/runtime and fixed-stage pipeline move here.
The package keeps the internal name `protocol_lab` to minimize semantic churn;
`formal_spec_agent` is the provider-neutral public CLI and optional role layer.

The mixed old `flow.py` was reduced by AST selection: only the unchanged
`TraceContractMismatch` and `run_scenario` definitions remain. Packetdrill,
Linux configuration, TCP builders, packet codecs and all protocol models remain
with TCPIP-Model. Legacy TCP-specific `wire` bindings explicitly fail admission
and C generation rather than failing later by an omitted import. Raw protocol
bytes explicitly built in IR need no such codec.

TCPIP-Model retains its original interpreter/backend as a **frozen historical
compatibility snapshot**. Old evidence binds that exact source; the snapshot
must not become another evolving generic implementation. New framework clients
use a pinned Git submodule in a separate process, with its own source/evidence
namespace. The new CLI never silently verifies an old run with a new checker.
New generic work is maintained only in Formal-Spec-Agent, then consumed by an
explicit pin update and newly executed benchmark checks. There is no circular
submodule dependency and no copy of the TCP model tree here.

The initial extraction does not claim semantic/compiler equivalence merely from
copying hashes. Tests exercise non-TCP reference/C/Z3/evidence/tamper boundaries;
external TCP/UDP tasks demonstrate data separation. Old full-protocol UNKNOWNs,
coverage gaps and implementation Differences stay in their original repository.
Future MCP/Skill/harness integrations can call the CLI; none is required now.
