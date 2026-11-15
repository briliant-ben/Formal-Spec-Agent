# Read/conditional C-expression correspondence, revision 1

The selected IR assignment returns data[index] when enabled and the index is
nonnegative and in range, otherwise zero. The IR owns the behavior. The native
artifact is produced by the existing independent C99 generator. Frozen literals
require nonzero valid delivery, negative/outside zero, disabled zero and octet255.

This unit proves a typed pure C-expression value model corresponds to the IR
fragment. Runtime helper/ABI contracts and the C parser/reifier are trusted.
Native contexts have octet buffers of at most4096 bytes, signed64 integers and
boolean fields encoded as0/1. No C memory/compiler/scheduler/error/whole-EFSM
proof is claimed; unselected code remains outside the certificate.
