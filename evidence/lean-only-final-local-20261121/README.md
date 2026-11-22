# Lean-only endpoint recheck

Framework revision `1ba0c022005e4bc5ed91d43609398078e5a8d5c2` freshly checked
the published IPv4 endpoint using Lean 4.35.0, Python `-S` and no solver
package. The case's pinned `make formal` command returned zero.

The 90 compiled modules establish initial admission, all 335 raw firings,
18 guard-conflict groups, timer advance and successful-or-uncovered dispatch
from admitted snapshots. The axiom audit contains only `propext`,
`Classical.choice` and `Quot.sound`. This is an invariant and scheduler proof,
not a compiler, full protocol, reachability or English specification proof.

The receive proof is split by its original two overlap cases and three link
phases. Each lemma keeps the original kernel heartbeat allowance; the existing
60-second per-module deadline is unchanged. The previous Linux timeout remains
in `../lean-linux-timeout-20261121` and is not upgraded by this run.

`proof.tar.gz` retains 273 original model, Lean, log and receipt files. Compiled
object files are excluded. `manifest.json` binds every retained file and the
archive. The public read-only inspector checked the retained bindings and
axiom report without executing retained source or native code. The separate
case suite passed all seven tests, including C compilation, frozen observations,
proof receipt bindings and recorded demo reconstruction.

The earlier no-Z3 flow comparison of 77 cases retains its own evidence and
`unresolved` exploration verdict. This check does not change the historical
UNKNOWN results or improve the declared 10/335 exploration coverage.
