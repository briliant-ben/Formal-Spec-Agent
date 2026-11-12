# Bounded byte mailbox, revision 1

This is a synthetic framework contract, not an Internet protocol. In READY, publish(data) admits up to eight octets, stores their exact content and emits delivered(data). Clear empties the stored buffer and emits nothing. Larger inputs are model gaps. No timers, network, delivery reliability or real peer is claimed.
