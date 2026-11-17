# Total integer-time batch scheduling

## Contract

Protocol IR alone declares guards, actions and invariants. Advance executes every
due timer at its exact deadline in lexical-name order, including newly rearmed
positive integer deadlines, then moves time to the target. Dispatch validates an
external event before advancing; tick checks final invariants. On any failure the
whole call preserves its original store, state, timers, clock and trace, including
removing successful timer prefixes. Output order and complete byte/string values
are observable. There is no arbitrary scheduler fuel or silent step cutoff.

Expected values were handwritten independently before executing the candidate.
The cases include a second-timer failure, external failure after two timer firings,
rearm at2/4/6 then pure clock to10, ties, injection and4096 exact bytes/Unicode/NUL.
Generic termination/progress is separate from protocol preservation before final
invariant filtering, compiler correctness and specification interpretation.
