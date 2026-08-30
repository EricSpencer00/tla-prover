---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES token, inCS, parent, requester, waiting

vars == <<token, inCS, parent, requester, waiting>>

TypeOK ==
  /\ token \in 0..R
  /\ inCS \in [Node -> BOOLEAN]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ requester \in Node
  /\ waiting \subseteq Node

Init ==
  /\ token = 0
  /\ inCS = [n \in Node |-> FALSE]
  /\ parent = [n \in Node |-> NoNode]
  /\ requester = initiator
  /\ waiting = {}

Request(n) ==
  /\ n \notin waiting
  /\ waiting' = waiting \cup {n}
  /\ UNCHANGED <<token, inCS, parent, requester>>

Grant(n) ==
  /\ n \in waiting
  /\ parent[n] = NoNode
  /\ token < R
  /\ \E p \in Node:
       /\ p # n
       /\ parent' = [parent EXCEPT ![n] = p]
  /\ token' = token + 1
  /\ waiting' = waiting \ {n}
  /\ UNCHANGED <<inCS, requester>>

Enter(n) ==
  /\ parent[n] # NoNode
  /\ ~inCS[n]
  /\ inCS' = [inCS EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<token, parent, requester, waiting>>

Exit(n) ==
  /\ inCS[n]
  /\ inCS' = [inCS EXCEPT ![n] = FALSE]
  /\ parent' = [parent EXCEPT ![n] = NoNode]
  /\ UNCHANGED <<token, requester, waiting>>

Next ==
  \/ \E n \in Node: Request(n)
  \/ \E n \in Node: Grant(n)
  \/ \E n \in Node: Enter(n)
  \/ \E n \in Node: Exit(n)

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node: n # initiator => parent[n] # NoNode
  /\ ~\E f \in [1..3 -> Node]: /\ f[1] = initiator /\ \A i \in 1..2: f[i+1] = parent[f[i]]

TestSpec == Spec /\ AncestorProperties

====