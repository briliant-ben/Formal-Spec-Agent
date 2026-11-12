# Proposal roles and trusted validation

The public interface is files and CLI, not a particular agent SDK. Deterministic
validation never requires a model provider. `propose` is an optional initial
role executor, not a self-integrating autonomous implementation loop.

A `formal-spec-proposal-job-v1` job has exactly `schema`, `id`, `sources`, `roles`.
Each source has relative `path` and `sha256`; each role has `id` and an explicit
text `messages` list using system/user/assistant roles. One to four independent
roles receive the same pinned specification data. A typical pair is a modeler
and an independent interpretation reviewer. They do not share evolving memory,
edit workspaces, execute source or count their own claims as validation.

The operator supplies the job digest, model name, credential location, immutable
candidate workspace, fresh output directory and shared original request ledger.
The controller rejects path escapes, changing inputs, duplicate roles/sources,
invalid messages and oversized prompts. Input changes during a call invalidate
the whole result. Failed/uncertain provider responses are terminal; the same
request is not automatically paid for again. The ledger uses lock/write-ahead
admission and is not reset when a job changes. Provider response text is JSON data.

All role results require controller review even if a model returns accepted=true.
An approved candidate is submitted through the independently pinned ten-stage
`run` task. No new oracle, scope or proof budget is implicitly approved by an LLM.
Multiple callers use independent candidate and output directories, with a shared
ledger only for the provider. This is process/source isolation, not a security
sandbox for arbitrary hostile native code. The current POSIX worker boundary,
compiler, Python, Z3, source interpretation and code translation remain trusted
components. Credentials and private provider records never belong in Git.
