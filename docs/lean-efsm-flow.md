# All-rule contracts in the ten-stage flow

Task-v6 explicitly selects `formal.strategy="lean-efsm"`, `formal.task`, the
approved contract digest and `formal.proofs`. Both files must be source-pinned,
and the contract must name the flow's exact model. Every workspace dependency of
the contract must also be in the flow snapshot. Other fields, including BMC depth
or solver tactics, are rejected for v6. Historical solver task versions require
their original pinned Git checker; the maintained package explicitly rejects them.

The trusted EFSM adapter checks IR0.5/0.6 atomic-v1, timer-free integer variables
and external integer events. It represents variable/event slots by declared
order and refuses unsupported syntax. All invariants are reified. It emits one
preservation obligation per rule, one overlap obligation per competing pair,
and coverage for every state × event, including empty groups. No guard is removed
or prioritized. Every rule additionally needs an admitted enabling witness and
an independently frozen literal outcome. Initial validity is a separate goal.

Preservation is quantified over a complete typed context: one unrestricted Lean
Int binder per model variable and event field. Store/environment lists therefore
have schema-correct dimensions. The exact guard and pre-invariants are hypotheses;
the conclusion evaluates every invariant on the ordered action result and target
state. It never assumes a valid poststate or calls the filtering transaction
dispatcher. A rule writing an invalid result cannot pass because runtime rollback
would hide it. Coverage and disjointness have independent universal obligations;
enabling/literal witnesses do not restrict their domains.

The v6 snapshot includes the entire generic Python/Lean/toolchain source set in
a separate framework namespace. The worker runs this fresh frozen trusted code,
not a different installed adapter. All raw Lean sources, proof data, kernel logs,
axiom audits and source identities are bound to the formal-stage report. The
remaining reference/test/C/build/execute/compare/traceability stages are unchanged.

`checked_efsm_contract` is a scoped model-contract result. Missing Lean produces
blocked/environment, compilation timeout produces unknown/resource_unknown,
false proofs fail, unsupported semantics reject. There is no Z3 fallback. The
aggregate verdict still distinguishes pass, unresolved, blocked and failed.

Retained `verify` checks all file hashes, namespace coverage, current source/task
bindings, reconstructed approved/proof sources, audit records, command prefixes
and proof-type flags. It does not run archived code, ELFs, Lean or a solver, and
does not establish historical authenticity. A trusted CI/provenance channel is
still needed. `lean-verify` separately performs fresh kernel checking. An
incomplete timed-out checker prefix may be retained as unresolved, never promoted
to a completed EFSM certificate.

The mathematical EFSM proof view is trusted translation of the authoritative IR;
it is not a proof of the Python interpreter, generic dispatcher, scheduler or C
compiler. It does not prove reachability, liveness, termination, standard-to-IR
interpretation, timers, bytes or native arithmetic/memory behavior. These remain
separate requirements for revalidating
the TCP/IP case under Lean.
