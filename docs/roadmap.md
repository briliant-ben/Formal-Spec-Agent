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

## Next: implementation correspondence

Formalize a typed IR expression/statement fragment and its evaluation contract.
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
