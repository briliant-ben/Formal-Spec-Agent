# Initial extraction qualification

61 actual local tests pass on Python3.12/Z3 4.15.4, including non-TCP ten-stage
reference/C/Z3/evidence execution, literal byte oracle, corruption rejection,
timer replay, rational arithmetic and initial reduction. The earlier Python3.9/
missing-Z3 environment failure is retained, not reclassified as passing.

`external-tasks.json`, `tcp-verify.json`, `udp-verify.json` retain actual external
TCPIP-Model task identities and results using the NEW framework, not old checker
results transplanted as new runs. All ten stages pass for TCP active-open and UDP
header descriptor. These are event-level implementation checks, not live network
or complete TCP/UDP claims. Original protocol files stay in TCPIP-Model.

DeepSeek0222 reviewed the initial controller/core extraction source and returned
empty blocking/findings/limitations. The original input/controller/public response
are in `framework-review-0222.tar.gz`, with an external per-member SHA manifest.
This source review does not establish correctness or execution authenticity.
Afterward the controller's source/job reads were tightened to hash the SAME bytes
used as model context, avoiding a hash/read race; final local tests pass. No
provider retry or automatic code execution/approval was added.

The added source-edit negative test first compared a macOS /var path with its resolved /private/var identity; the failing assertion is retained. It now compares the canonical path actually required by the API; no source-change invalidation rule was weakened.
