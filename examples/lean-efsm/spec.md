# Scalar mailbox, revision 1

Two states EMPTY/FULL; integer slot initially0/EMPTY. EMPTY requires slot=0.
FULL requires 1<=slot<=255. put(value) for 1..255 stores value, enters FULL
and emits stored(value), replacing any old value. Other integer put values
leave state/slot unchanged and emit rejected(input). take in FULL emits
delivered(old slot), clears slot to0, enters EMPTY. take in EMPTY emits
missing(0) and stays EMPTY. Mathematical integers; no timers, bytes or overflow.
Rules must be disjoint and cover every integer put and take in each admitted
state. Preservation is required before runtime invariant filtering.

Frozen sequence: take->missing0; put65->stored65/FULL65; put255->stored255/FULL255;
put256->rejected256/FULL255; take->delivered255/EMPTY0; put0->rejected0/EMPTY0.
Enabling witnesses are not reachability proofs. Finite coverage is not universal
protocol, specification interpretation or compiler correctness.
