# Lean replay of the recorded TCP/IP peer session

The fixture preserves the successful baseline's 19 input operations from
`live/scenario.json`, with expected results from the generated C subject's
raw stdout. The conversion checks the archived session operation boundaries
and equality with the archived Difference report. The archive is the original
Linux virtual-link run from the TCP/IP case study. The evidence here comes
from offline execution of the Lean interpreter against that recording.

The first Lean build exhausted its elaboration budget in `Runner.lean`. Using
a declaration per input operation preserved both the model source and the
case digest. The resulting executable matched the observed rule, input
fields, stored variables, timers, emissions and final state of each of the
19 operations. The input fixture and Lean compiler output are bound by the
[manifest](manifest.json).

The archive contains the first failure, successful result, original
conversion script and selected source and stdout. It also retains the
complete timed proof audit and runtime regression logs. The kernel proof
covers the pinned IR. The replay measures correspondence for these recorded
inputs.
