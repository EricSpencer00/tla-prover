---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, phase, echoCount, active

vars == <<parent, phase, echoCount, active>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ echoCount \in [Node -> 0..Cardinality(Node)]
  /\ active \in BOOLEAN

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> IF n = initiator THEN "active" ELSE "idle"]
  /\ echoCount = [n \in Node |-> 0]
  /\ active = TRUE

SendEcho(n, m) ==
  /\ phase[n] = "active"
  /\ m # n
  /\ <<n, m>> \in R
  /\ phase[m] = "idle"
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ phase' = [phase EXCEPT ![m] = "active"]
  /\ echoCount' = [echoCount EXCEPT ![n] = echoCount[n] + 1]
  /\ UNCHANGED active

Reply(n) ==
  /\ phase[n] = "active"
  /\ \A m \in Node : (<<n, m>> \in R) => phase[m] # "idle"
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, echoCount, active>>

Terminate ==
  /\ \A n \in Node : phase[n] = "done"
  /\ active' = FALSE
  /\ UNCHANGED <<parent, phase, echoCount>>

Next ==
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E n \in Node : Reply(n)
  \/ Terminate

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => (parent[parent[n]] # NoNode)
  /\ \A n \in Node : (n # initiator /\ parent[n] # NoNode) => (n \notin {parent[m] : m \in Node})

TestSpec == Spec

====