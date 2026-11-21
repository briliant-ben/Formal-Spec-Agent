# Original full-job cancellation and transmit timeout

The original artifact from run 44917864818, job 136887240414, is retained
unchanged. Its archive hash and source head are in `manifest.json`.

The original receive split passed far enough to reach `TCPIPTransmit`, which
retained `resource_unknown` after the unchanged 60-second module deadline.
The suite continued, then the 15-minute CI job deadline cancelled it during
another test. There is no completed full-suite pass to infer from that job.

The follow-up splits the original send proof into layout, control, bounds,
link-phase, certificate and catalog modules. The link proof uses its original
first/continuing and empty/pending/resolved cases. It retains every rule,
invariant and the original kernel heartbeat allowance. CI partitions the same
155 tests into 154 general tests and one endpoint proof test, each with the
existing job and module limits. No test, formula or input domain is removed.
