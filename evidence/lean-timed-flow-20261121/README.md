# Timed Lean verification of the IPv4 closeout flow

The run used the original 66 pinned scenario seeds and the original
exploration domain. The task was upgraded to the reviewed Lean timed
strategy. The Python environment contained no Z3 package.

The formal stage passed for 335 firings and 18 conflict groups. Reference
execution, C generation and compilation, native execution, comparison and
traceability passed. The comparison checked 77 cases. The declared exploration
found 10 of 335 rules, so the overall result remains `unresolved`.

The [manifest](manifest.json) binds selected original files. The retained
integrity audit covered 223 inputs and all 1052 output artifacts in the
original run directory. The selected archive contains the formal report,
kernel audit, generated proof statements, comparison stage and flow report.
The first attempt's Lean export was rejected for missing theorem type
annotations. Its source and diagnostic are included with their original
verdict.
