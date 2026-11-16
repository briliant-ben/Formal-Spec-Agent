# Independent review and controller disposition

DeepSeek produced two completed proof-data proposals (jobs 0229 and 0230).
Both failed actual Lean checking. The controller repaired the proof data using
the reported errors and added a nonzero native-context admissibility obligation.
The final accepted proof is therefore not attributed solely to the model.
Job 0231 independently reviewed the reifier. Its original response is retained
in `deepseek-review.json`; its labels are advice, not kernel findings.

| Review item | Controller disposition / evidence |
|---|---|
| Future grammar relaxation | No current counterexample. Added the parser source digest to the frozen task, with an epoch-change rejection test. |
| Macros redefining m/f/bf | Runtime/harness are pinned, and extra preprocessing is refused. Added all three macro mutations to regression tests. A deliberately changed trusted runtime requires new approval; its correctness is not proved. |
| Indices above signed64 | Outside the explicit native admission contract. Added rejected out-of-domain witnesses and admitted endpoint tests. Total mathematical evaluation does not expand the ABI claim. |
| Impure shared helper | Unknown calls and additional statements are rejected. Added a concrete impure-return regression. |
| Draft approval bypass | Draft output cannot pass the frozen approval check. Added a draft/self-approval regression. |
| Helper variable capture | Accepted helpers have fixed formals, unchanged arguments, no local declarations and one pure return. No admitted capture counterexample was supplied. |
| Implicit conversions / suffixes | Unsupported spellings are deliberately refused. This is incomplete C acceptance, not a certificate for those expressions. |
| Side channels / loops / writes / failure | Outside the selected pure expression's value contract. The certificate does not cover surrounding statements, memory, timing or compiler transformations. |

Controller lexical review also added rejection of unterminated strings/comments
and non-ASCII source. The native reference compiler initially could not create
temporary files under its minimal environment; its runner now supplies a fresh
explicit temporary directory. The original failed run is retained separately.
Neither issue was resolved by weakening a proof or changing expected outputs.

Known usage from the three receipts: 4,284 + 7,074 + 10,487 = 21,845 tokens.
No failed/uncertain API call was retried. Only completed source proposals were
repaired from concrete checker errors. Credentials and model reasoning are absent.
