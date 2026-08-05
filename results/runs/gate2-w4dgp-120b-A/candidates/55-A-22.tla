---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS
  Node, initiator, R, NoNode

ASSUME /\ initiator \in Node
       /\ NoNode \notin Node

VARIABLES parent, active

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ active \subseteq Node

TreeReachesAll ==
  /\ \A n \in Node \ {initiator} : \E p \in Node : parent[p] = n
  /\ \A n \in Node : (n # initiator /\ parent[n] = NoNode) => FALSE

Init ==
  /\ parent = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]
  /\ active = {initiator}

Echo(n, m) ==
  /\ n \in active
  /\ m \in R
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ active' = active \cup {m}
  /\ UNCHANGED <<>>

Relay(n, m) ==
  /\ n \in active
  /\ parent[n] # NoNode
  /\ m \in R
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ active' = active \cup {m}
  /\ UNCHANGED <<>>

Next ==
  \/ \E n \in Node, m \in R : Echo(n, m)
  \/ \E n \in Node, m \in R : Relay(n, m)

PrintEdges ==
  /\ UNCHANGED <<parent, active>>
  /\ \A a \in R : Print(Pair(a[1], a[2]))

Spec ==
  /\ Init
  /\ [][Next]_<<parent, active>>

TestSpec ==
  /\ Init
  /\ [][Next]_<<parent, active>>
  /\ []PrintEdges

====