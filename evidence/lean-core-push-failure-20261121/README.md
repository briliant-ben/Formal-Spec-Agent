# Original push-only mailbox flow failures

PR run 44919909904 passed all 155 tests, while push run 44919903813
passed the complete endpoint proof and CLI but failed two mailbox flow
assertions in its 154-test core partition. The original log is retained
unchanged. Both assertions report assessment failed; their temporary stage
bundles were removed by the old tests, so the specific cause is not known.
Do not infer a proof or timing failure from those assertions alone.

The follow-up preserves original flow output before cleanup and prints
failed stage data. No timeout, task, model, proof or expected verdict changes.
