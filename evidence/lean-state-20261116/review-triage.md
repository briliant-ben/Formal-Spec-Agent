# Proposal, review and controller disposition

Job 0232 returned a completed proof-data proposal (3,139 known tokens). The
restricted renderer rejected its empty proof branches before executing Lean.
The controller repaired the generic proof instructions. The first repair then
failed actual Lean on unreduced let-bindings and an unresolved List.set lookup.
The final repair uses restricted `dsimp` and an explicit bound lemma. Eleven
obligations passed. The semantic definitions, frozen outcomes and theorem
statements were not weakened to accept a proposal. Original rejections remain.

Job 0233 returned an independent review (16,132 known tokens), with sixteen
items labeled blocking. These labels do not approve or veto a candidate by
themselves. Each item was checked against current source and actual execution:

| Item | Disposition |
|---|---|
| 1: invariants use no event environment | Intentional state-only invariant semantics; event references are refused. |
| 2: List.set proof may fail | Actual Lean 4.35.0 accepted the repaired bound-lemma proof. The original failed attempt remains. |
| 3: exact task keys | Intentional strict versioned schema. |
| 4: task path admission | Already resolved and checked inside the workspace. |
| 5: transitive base ordering | Inspected `model_files`: first current model, recursively followed by bases. Every base must be source-pinned. |
| 6: total out-of-bounds semantics | Adapter generates in-schema indices; witnesses require exact store/environment dimensions. Generic read-after-write theorem has an explicit bound premise. No native-memory claim. |
| 7: invariant order | Preserved by list construction. |
| 8: witness reduction may fail | All eleven actual kernel goals pass; mutants fail. |
| 9: self-loop restriction | Deliberate; actual source compares selected rule's from/to, not a presumed first rule. |
| 10: model initial values | Action-block claim uses explicit witness stores, each separately proved admitted; no default-EFSM-initialization claim. |
| 11: witness field dimensions | Explicitly checked. |
| 12: omitted relational operators | Explicit rejection, not ignored obligations. |
| 13: trivial invariants | Both accepted and rejected witnessed outcomes are mandatory. An always-true contract cannot prove the rejected outcomes; false admission is tested and fails. |
| 14: missing adapter identity | Already included in task pin and result input hashes. |
| 15: draft approval | Drafts cannot pass normal frozen approval. |
| 16: certificate type/status | Separate scoped status and flags. Controller additionally hardened fresh verification against forged scope/C/compiler claims; tests mutate all four. |

No concrete admitted counterexample was supplied by those sixteen items; many
review sentences explicitly retract their own concern. Limitations about integer
types, one-field emissions, guard/timer selection and native C correspondence
are retained in documentation. The review is not a theorem or model approval.

The base package was installed independently with no Z3 present. Actual Lean
units and Lean-to-C reference execution passed there. An actual old mailbox run
reported its Z3 formal stage blocked/environment while reference/native compare
passed; no backend fallback or proof promotion occurred.

There were two paid completed requests, 19,271 known tokens total, using the
original shared ledger. No failed/uncertain API was retried, and no key or model
reasoning is included. An initial installation used the host's Python 3.9 and was
rejected by the package's >=3.11 requirement; the accepted fresh environment
uses Python 3.12. This environment failure was not counted as validation.
