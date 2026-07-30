---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

InitEdges ==
  { <<a, b>> : a \in Node, b \in Node, a # b }

VARIABLES parent, active, done, echo
vars == <<parent, active, done, echo>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ active \subseteq Node
  /\ done \subseteq Node
  /\ echo \in [Node -> [cnt : 0..2]]

AncestorProperties ==
  /\ initiator \in done
  /\ \A n \in done : n = initiator \/ parent[n] \in done
  /\ \A n \in Node : (parent[n] = NoNode) <=> (n = initiator)

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ active = {}
  /\ done = {initiator}
  /\ echo = [n \in Node |-> [cnt |-> 0]]

Activate ==
  /\ \E n \in Node :
       /\ n \notin active
       /\ n \notin done
       /\ \E q \in Node :
            /\ <<q, n>> \in R
            /\ parent' = [parent EXCEPT ![n] = q]
       /\ active' = active \cup {n}
  /\ UNCHANGED <<done, echo>>

Reply ==
  /\ \E n \in active :
       /\ n \notin done
       /\ active' = active \ {n}
       /\ done' = done \cup {n}
       /\ echo' = [echo EXCEPT ![n].cnt = 2]
  /\ UNCHANGED parent

TestSpec == Init /\ (Activate \/ Reply)

Spec == TestSpec

====