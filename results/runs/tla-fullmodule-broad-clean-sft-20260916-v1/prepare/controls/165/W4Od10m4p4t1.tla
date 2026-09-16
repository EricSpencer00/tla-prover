---- MODULE W4Od10m4p4t1 ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Capacity, MaxId

\* A signalling block holds a bounded buffer (queue) of pending movement-
\* authority messages plus a set of messages already dispatched downstream
\* but not yet acknowledged (inflight). Both occupy the block's physical
\* capacity until acknowledged, since the block cannot be released early.
VARIABLES queue, inflight, acked, nextId, backpressure

TypeOK ==
  /\ queue \in Seq(1..MaxId)
  /\ inflight \subseteq 1..MaxId
  /\ acked \subseteq 1..MaxId
  /\ nextId \in 1..(MaxId + 1)
  /\ backpressure \in BOOLEAN

Init ==
  /\ queue = <<>>
  /\ inflight = {}
  /\ acked = {}
  /\ nextId = 1
  /\ backpressure = FALSE

\* Enqueue a fresh message only if the block still has spare capacity once
\* both buffered and inflight (unacked) messages are counted together.
Enqueue ==
  /\ nextId <= MaxId
  /\ Len(queue) + Cardinality(inflight) < Capacity
  /\ queue' = Append(queue, nextId)
  /\ nextId' = nextId + 1
  /\ UNCHANGED <<inflight, acked>>
  /\ backpressure' = (Len(queue') + Cardinality(inflight') >= Capacity)

\* Twist: messages in the buffer may be reordered before they are
\* dispatched, modeling out-of-order delivery/processing on the block.
Reorder ==
  /\ Len(queue) > 1
  /\ \E i \in 1..(Len(queue) - 1):
       queue' = [queue EXCEPT ![i] = queue[i+1], ![i+1] = queue[i]]
  /\ UNCHANGED <<inflight, acked, nextId, backpressure>>

\* Dispatch the head of the buffer downstream; it still occupies capacity
\* as an inflight message until acknowledged.
Dispatch ==
  /\ Len(queue) > 0
  /\ queue' = Tail(queue)
  /\ inflight' = inflight \union {Head(queue)}
  /\ UNCHANGED <<acked, nextId>>
  /\ backpressure' = (Len(queue') + Cardinality(inflight') >= Capacity)

\* Acknowledgments may arrive out of order too (the twist applies
\* downstream as well): any inflight message can be acked next.
Ack ==
  /\ inflight # {}
  /\ \E m \in inflight:
       /\ inflight' = inflight \ {m}
       /\ acked' = acked \union {m}
  /\ UNCHANGED <<queue, nextId>>
  /\ backpressure' = (Len(queue') + Cardinality(inflight') >= Capacity)

Next == Enqueue \/ Reorder \/ Dispatch \/ Ack

Spec == Init /\ [][Next]_<<queue, inflight, acked, nextId, backpressure>>

\* SAFETY: the signalling block's occupied capacity -- buffered plus
\* inflight unacknowledged messages -- never exceeds its physical bound,
\* regardless of how messages are reordered or acknowledged out of order.
CapacityInvariant == Len(queue) + Cardinality(inflight) <= Capacity

====