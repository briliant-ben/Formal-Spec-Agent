# Pure typed values, revision 1

The authoritative IR fixes five value types and 26 operators used by the compact
IPv4 case. Integers are mathematical, sequence numbers are residues modulo2^32,
byte buffers preserve octets, strings preserve Unicode scalar content. Negative
slice offset/count clamp independently; byte reads outside the buffer return0.
Packing is big endian modulo8/16/32bits, including negative integers.

RFC1071 section1 describes adjacent big endian words, odd final high octet with
zero low octet, repeated end-around carry and complement. This arithmetic operator
does not add UDP absent-checksum or zero-toFFFF policy. RFC9293 section3.4 requires
modulo2^32 sequence arithmetic. The IR totalizes addition for all Int offsets;
RFC1982 section3.1 has a narrower defined addition domain, so these are not claimed
equivalent outside that domain. At half-space, comparable/lt/le are false; callers
must not use that as a defined RFC ordering. Timer membership is a pure context
query here, without a scheduler/deadline proof.

Sources: https://www.rfc-editor.org/rfc/rfc1071.html#section-1
https://www.rfc-editor.org/rfc/rfc9293.html#section-3.4
https://www.rfc-editor.org/rfc/rfc1982.html#section-3.2

Frozen values below are independent arithmetic literals, not regenerated from
the subject/reference. The certificate checks selected expression values and a
typed shared view; not EFSM transitions, C, compiler or full protocol correctness.
