# Framework milestones

## Implemented baseline

- Declarative Protocol IR, independent reference/Z3 checks, generated tests,
  standalone C, exact observations/Difference and source traceability.
- Optional independent DeepSeek proposal roles, pinned inputs and a persistent
  request ledger. Responses cannot self-approve or execute model-returned code.
- Compact C expression factoring with retained semantics/failure regressions.
- Optional Lean expression-contract pilot: frozen source/statement hashes,
  proof-data-only workers, actual Lean 4.35.0 checks, a separate axiom audit,
  positive witnesses, mutation/tamper rejection and fresh certificate rechecking.

These are finite, explicit scopes. A passing expression unit is not a proof of
its containing EFSM, the generated C compiler, an Internet standard or TCP/IP.
Existing UNKNOWNs and implementation Differences remain independent evidence.

- A first typed IR / actual C-expression correspondence unit under pinned
  runtime/ABI contracts, with helper expansion, malformed-code rejection and
  rebound-mutant tests. Optional compiled Lean → C reference execution is real,
  but requires Lean's runtime and does not certify either native compiler.

## Next: implementation correspondence

The compact case's five types and 26 pure operators are now represented by typed
Lean data and evaluated by a pure interpreter. Complete case expression typing,
59 kernel obligations and compiled reference values are separate claims. Exact
long-buffer content is preserved, and timer membership is not scheduling. See
[typed values](lean-typed-values.md). Extend this layer to transition effects and
timer scheduling next; the whole335-rule EFSM is not yet certified.

An all-rule timer-free integer EFSM contract now feeds the complete ten-stage
flow through explicit task-v6. It checks preservation before runtime filtering,
disjointness, total state/event coverage, initial validity and admitted literal
witnesses. This is a larger proof boundary than the earlier selected action block;
it still excludes timers/bytes/native arithmetic and interpreter/compiler proofs.
See [Lean EFSM flow](lean-efsm-flow.md). Next extend value/operator coverage,
then scheduling, before migrating TCP/IP and retiring the optional backend.

Lean-first installation no longer requires Z3. An integer, timer-free action-block
unit now checks ordered set/emit and final-invariant rollback. See the
[capability gates](lean-first.md) before retiring the optional solver backend.
Neither milestone replaces whole-EFSM checking or proves C statements.

Extend the typed pure expression fragment to statements and its evaluation contract.
Establish a checked connection to a C subset or per-output translation validation,
starting with byte access/slices and conditional evaluation. Then cover ordered
updates, failures/rollback and expression factoring. Keep all protocol decisions
in the single authoritative IR; derived proof views are not another protocol spec.

## Next: broader, independently scored benchmark

Add several small protocols beyond the byte unit and mailbox. Freeze source
interpretations, supported domains, normal-run witnesses and adversarial cases.
Score modeling, implementation generation, proof obligations and fault detection
separately. Reachability, nonvacuity, invariant preservation and delivery are
separate claims. Specification amendments require a reviewed new approval epoch.

## Next: persistent provider-neutral agent controller

Build an obligation/dependency queue over the deterministic interfaces. Give
workers isolated candidate state and explicit allowed edits; use bounded tool
feedback and a single integrator. Cache completed obligations by complete input,
semantics and checker identity. Expose the same workflow to CLI, MCP, Skills or
other agent harnesses. Failed/uncertain provider calls remain terminal rather
than being silently paid for again. The checker, not an agent, owns completion.
