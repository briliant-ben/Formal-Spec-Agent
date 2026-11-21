# Original closed-transition resource failure

The push channel retained a 60-second module timeout in TCPIPClosedTransitions.
The same revision passed the independent PR channel; neither result overwrites
the other. The original ZIP and its digest are retained. The follow-up divides
the same helper, rule and catalog declarations into separate compilation units,
without changing any rule, invariant, heartbeat option or deadline.
