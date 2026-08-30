---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node

VARIABLES parent, visited, crossing, acks

vars == <<parent, visited, crossing, acks>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ visited \subseteq Node
  /\ crossing \subseteq (Node \X R)
  /\ acks \subseteq (Node \X Node \X R)

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node \ {initiator} : initiator \in (n ^* parent)
  /\ \A x, y, z \in Node : (z \in (y ^* parent) /\ y \in (x ^* parent)) => z \in (x ^* parent)

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE initiator]
  /\ visited = {}
  /\ crossing = {}
  /\ acks = {}

SendStart(n, r) ==
  /\ n \notin visited
  /\ <<n, r>> \notin crossing
  /\ \E m \in Node : <<m, r>> \notin crossing
  /\ crossing' = crossing \cup {<<n, r>>}
  /\ UNCHANGED <<parent, visited, acks>>

Ack(m, n, r) ==
  /\ <<m, r>> \in crossing
  /\ m # n
  /\ crossing' = crossing \ {<<m, r>>}
  /\ acks' = acks \cup {<<m, n, r>>}
  /\ UNCHANGED <<parent, visited>>

Adopt(n, m, r) ==
  /\ <<m, n, r>> \in acks
  /\ n \notin visited
  /\ visited' = visited \cup {n}
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ acks' = acks \ {<<m, n, r>>}
  /\ UNCHANGED crossing

Next ==
  \/ \E n \in Node, r \in R : SendStart(n, r)
  \/ \E m, n \in Node, r \in R : Ack(m, n, r) \/ Adopt(n, m, r)

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ (\A n \in Node, r \in R : SendStart(n, r))

\* Graph must be fully meshed over Node with no self-loops.
N1 == Node
I1 == initiator
R1 == R

====