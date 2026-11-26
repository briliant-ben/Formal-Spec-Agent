# C99 Embeddable Library Backend (`c99-lib-v1`)

`formal-spec-agent codegen-lib` lowers an admitted Protocol IR model into a freestanding-friendly, reentrant, zero-heap C99 state-machine library (`<prefix>.h`, `<prefix>.c`, `fsa_lib_runtime.h`, plus `generation.json`).

Whereas `protocol_lab/codegen` (`v6`) targets standalone trace-runner executables with heap/stdio diagnostics and a linear rule scan, `formal_spec_agent/codegen_lib.py` (`c99-lib-v1`) targets embedded and stack-integrated C99 libraries such as `TCPIP-Model`'s `libtcpip.a`.

## CLI usage

```sh
formal-spec-agent codegen-lib model.json \
  --out /tmp/out-lib \
  --prefix tcpip \
  --byte-cap 2048 \
  --arena-cap 4096 \
  --fast-dispatch \
  --debug-names
```

Key flags:

- `--prefix <ident>`: sets C type/symbol prefix (`<prefix>_machine_t`, `<prefix>_init`, `<prefix>_step`, `<prefix>_step_with_arena`, `<prefix>_tick`, `<prefix>_tick_one`, `<prefix>_next_due_ms`, `<prefix>_check_invariants`).
- `--fast-dispatch`: defaults `<PREFIX>_CHECK_CONFLICTS`, `<PREFIX>_ATOMIC_ROLLBACK`, and `<PREFIX>_CHECK_INVARIANTS` to `0` for Lean-proved EFSMs (any of these macros can still be overridden at compile time via `-D`).
- `--debug-names`: emits `<prefix>_{state,event,rule,msg,svar,bvar}_name(...)` lookup tables when human-readable tracing is wanted; omit for smaller `.rodata`/`.text`.
- `--byte-cap`, `--arena-cap`: bounds per-byte-variable storage inside `<prefix>_machine_t` and per-step scratch memory.

## Design highlights

1. **Zero `stdio` / zero `malloc` on the hot path**: uses `<stdint.h>`, `<stddef.h>`, `<string.h>`, and `<limits.h>` only, with caller-supplied stack/scratch `fsa_arena_t` and zero-copy `fsa_slice_t` slices.
2. **Decision-tree rule dispatch**: partitions rules by `(state, event)` and recursively splits on pure equality constraints (`switch (lhs)`), shrinking code size and eliminating linear rule scans on large protocols.
3. **Deduplicated shared pure expressions & static RO-data byte literals**: compound expressions appearing cleanly across multiple rules/actions are lowered once to shared helpers, and non-empty IR byte literals are interned once into `static const uint8_t` tables (avoiding stack compound literals inside helpers).
4. **Embeddable timer stepping**: supports both batch expiry (`<prefix>_tick`) and single-timer stepping (`<prefix>_tick_one` + `<prefix>_next_due_ms`) for event loops and deterministic trace harnesses.
5. **Callback semantics**: when `ATOMIC_ROLLBACK=1`, failing inside a transition rolls back machine state `*m`, while any prior completed timer firings during `<prefix>_advance` have already invoked `on_emit` for their committed transitions. All `emit` expressions are validated even when `on_emit == NULL`.

## Baseline verification (`TCPIP-Model` legacy 24-path / 157-transition regression)

Measured by `tests/test_codegen_lib.py` (`-std=c99 -Wall -Wextra -Werror -Os`):

| Target | `-Os` `.text` | Delta vs `v6` | Notes |
|---|---:|---:|---|
| `v6` (`code/generated/protocol.c`) | `414,562 B` | — | Standalone CLI trace runner |
| `c99-lib-v1` (strict, `--debug-names`) | `331,312 B` | `-20.1%` | Conflict checks + atomic rollback + invariants enabled |
| `c99-lib-v1` (`--fast-dispatch`) | `279,849 B` | `-32.5%` | Decision-tree fast path (`6` switches, `~227 ns/pkt` E2E subprocess bench) |

All 24 frozen regression paths and 157 transitions match the `v6` reference identically for emitted bytes, post-states, rules, and scalar variables in both strict and `--fast-dispatch` modes.
