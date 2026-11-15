# Lean expression proof gates (pilot v1)

Lean is an optional proof backend alongside the existing reference interpreter,
Z3 strategies, C generator and observation pipeline. Nothing upgrades old
UNKNOWN results, finite runs or recorded PCAP into Lean proofs.

## Exactly what is checked

The pinned checker is **Lean 4.35.0**, with Std and no mathlib dependency. This
pilot selects one integer assignment expression from atomic ordered IR 0.5/0.6.
It supports integer/boolean/byte literals, typed event fields, `bytes_slice`,
`bytes_at_or_zero`, `bytes_len` and `ite`. Other operators, state-variable reads,
clock/post semantics and full EFSM transitions are explicitly refused for this
unit. Unselected machine behavior is outside the proof claim, not proved safe.

The trusted Python adapter derives an `Approved.expression` directly from the
selected IR expression. Lean uses `List (Fin 256)` for finite octet buffers and
`Int` for IR integers. Negative slice offsets/counts clamp to zero; negative and
out-of-range reads return zero. There is no C memory, signed64 overflow, timer,
network environment, compiler or whole-protocol proof here. The adapter and
Lean semantic definitions remain trusted; their agreement with the interpreter
and native C is exercised on fixed independent literals, not universally proved.

Nine frozen obligations in the byte example cover universal byte-read bounds,
negative reads, slice length bounds, the selected expression's result range and
five concrete witnesses. A nonzero witness is mandatory: an always-zero mutant
can satisfy a range property but must fail delivery. This is expression
nonvacuity, not default-state reachability or transition-enable coverage.

## Approved inputs and untrusted proof data

A task pins the IR, source documents, semantic foundation and **exact generated
Approved.lean digest**. Its externally supplied SHA256 is the acceptance input.
`lean-plan` can render a proposed statement file, but returns only
`draft_requires_independent_approval`. Checking never silently accepts that draft.
Changing a specification, theorem definition or dependency requires a new,
explicitly approved task/checker epoch. A matching hash binds bytes; approval
still comes from the caller/controller, not a model or a locally computed hash.

Workers return JSON instructions from a finite proof-data language. The trusted
renderer owns every import, definition and theorem header. Supported steps are
`intro`, `unfold`, `simp`, `simp_all`, `omega`, `decide`, `rfl`, `assumption`,
`exact`, `apply`, `have`, two-branch `split`/`constructor`, and two-branch `cases`.
Terms are single-line restricted applications. Arbitrary Lean commands,
declarations, options, macros, quotation, IO and raw tactic scripts are refused.
Every frozen obligation needs exactly one nonempty proof. No worker can declare
success or edit the checked problem through its proof payload.

The controller reconstructs a fresh project. Foundation and approved statements
are read-only during checking. It compiles all modules with Lean, then compiles
a separate trusted audit that checks each proof against its frozen proposition
and prints its transitive axioms. Only `propext`, `Quot.sound` and
`Classical.choice` are allowed. Missing audits or any other axiom reject the run;
Lean accepting a term containing internal `sorryAx` is deliberately insufficient.
A source/input mutation invalidates the result. Missing Lean is `blocked`, a
failed proof is `fail`, and a timeout is `resource_unknown`, never a proof.

This is not a general security sandbox or an independent Lean kernel. The
approved framework, Python process, complete pinned Lean/Std installation,
loader, OS and audit logic are trusted. The binary hash/version is recorded;
version output alone does not attest all shared libraries or standard-library
files. Provider code receives neither credential data nor control of the checker.

## Run and recheck

Install an official Lean 4.35.0 toolchain. With elan, use `elan which lean` after
selecting that toolchain, or pass the actual release binary explicitly. Existing
framework installation requirements still apply.

```sh
TASK_SHA=$(shasum -a 256 examples/lean-bytes/task.json | cut -d ' ' -f 1)
formal-spec-agent lean-check examples/lean-bytes/task.json \
  --workspace examples/lean-bytes --proofs examples/lean-bytes/proofs.json \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/lean-byte-check-001
formal-spec-agent lean-verify /tmp/lean-byte-check-001 \
  --task examples/lean-bytes/task.json --workspace examples/lean-bytes \
  --task-sha256 "$TASK_SHA" --lean /path/to/lean-4.35.0/bin/lean \
  --out /tmp/lean-byte-recheck-001
```

Rechecking validates retained hashes, regenerates approved statements using the
current trusted pinned checker, and recompiles the JSON proof data in a fresh
project. It never executes archived Python or imports retained `.olean` files.
Old checker epochs require their original framework. The positive result is
`checked_expression_contract`; `protocol_correctness_proved` and
`compiler_correctness_proved` remain false. The ten-stage protocol flow and its
assessment are unchanged; this is an additional scoped certificate.

For a new unit, start with the documented task fields in the example. Fill
`approved_sha256` with a draft placeholder, run `lean-plan` with a fresh external
output, independently review its definitions/contracts/witnesses, then approve
the exact digest in a new task. Do not refresh witnesses from a failing subject.

## Next proof boundary

The next step is a formal IR expression/statement semantics and a checked
correspondence with a C subset or per-output translation validation. These
semantic lemmas alone do not prove the compact C generator, its expression
sharing, buffer ownership or the existing TCP/IP implementation correct.
