# Integer action transaction, revision 1

A selected timer-free READY self-loop accepts an integer input. Assign x from
the input, emit x, assign y from the current x, then emit y. Each assigned
value is visible to subsequent actions. Both variables must be in 0..255.
An invariant failure discards every tentative write and output; the externally
visible values and transition trace remain unchanged. Initial values are x=7,
y=3. Success input65 gives values[65,65] and outputs65,65. Inputs-1 and256 fail
without values or output. Input0 succeeds with values[0,0] and outputs0,0.

This is a finite acceptance fixture for a generic integer action-block model,
not a whole protocol or native compiler proof. No timer, guard resolution,
arithmetic, target-state change, bytes, native-capacity failure or scheduling.
