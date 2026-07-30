---- MODULE MCEcho ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, echoActive, phase

vars == <<parent, echoActive, phase>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ echoActive \in [Node -> BOOLEAN]
  /\ phase \in [Node -> {"passive", "active"}]

AncestorProperties ==
  /\ \A n \in Node : \A m \in Node : (n # m /\ parent[m] = n) => parent[n] # n
  /\ \A n \in Node : \A m \in Node : (n # m /\ parent[m] = n) => phase[n] = "active")
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode /\ phase[n] = "active")
  /\ parent[initiator] = NoNode

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ echoActive = [n \in Node |-> FALSE]
  /\ phase = [n \in Node |-> "passive"]

SendEcho(n, m) ==
  /\ phase[n] = "active"
  /\ m \in Node
  /\ m # n
  /\ <<n, m>> \in R
  /\ ~echoActive[m]
  /\ parent[m] = NoNode
  /\ echoActive' = [echoActive EXCEPT ![m] = TRUE]
  /\ phase' = [phase EXCEPT ![m] = "active"]
  /\ UNCHANGED parent

SetParent(m, n) ==
  /\ echoActive[m]
  /\ phase[m] = "active"
  /\ n \in Node
  /\ n # m
  /\ <<n, m>> \in R
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ UNCHANGED <<echoActive, phase>>

Deactivate(n) ==
  /\ phase[n] = "active"
  /\ \A m \in Node : parent[m] # n
  /\ phase' = [phase EXCEPT ![n] = "passive"]
  /\ UNCHANGED <<parent, echoActive>>

Next ==
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E m \in Node, n \in Node : SetParent(m, n)
  \/ \E n \in Node : Deactivate(n)

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ UNCHANGED vars /\ PrintAdjacency

PrintAdjacency ==
  /\ UNCHANGED vars
  /\ Print("Adjacency relation R = " ^ ToString(R))

\* The .cfg file overrides N1, I1 and R1 with bounded values; these
\* definitions exist only so the uninstantiated module type-checks.
N1 == Node
I1 == initiator
R1 == R

====