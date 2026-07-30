---- MODULE MCEcho ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

Nodes == CHOOSE S \in (SUBSET Node) : Cardinality(S) = 3

VARIABLES phase, parent, recv, ack, level
vars == <<phase, parent, recv, ack, level>>

TypeOK ==
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ recv \in [Node -> SUBSET Node]
  /\ ack \in [Node -> SUBSET Node]
  /\ level \in [Node -> 0..3]

Init ==
  /\ phase = [n \in Node |-> "idle"]
  /\ parent = [n \in Node |-> NoNode]
  /\ recv = [n \in Node |-> {}]
  /\ ack = [n \in Node |-> {}]
  /\ level = [n \in Node |-> 0]

TestEcho ==
  /\ \E x \in Node : x = initiator
  /\ \E h \in 0..3 : \A n \in Node : level[n] = h
  /\ phase[initiator] = "active"
  /\ \A n \in Node : phase[n] = "done" => parent[n] # NoNode

Spec == TestEcho

SpecAssumeInit == Spec /\ Init
SpecAssumeNext == Spec /\ Spec /\ UNCHANGED vars

SpecStep ==
  \/ SpecAssumeInit
  \/ SpecAssumeNext

\* The full set of actions states that the model checker is free to interleave
\* in any order; nothing is suppressed here.
Next ==
  \/ SpecStep
  \/ (SpecStep /\ UNCHANGED vars)

SpecCorrect == Spec /\ Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : phase[n] = "done" => (n # initiator => parent[n] # NoNode)
  /\ \A n \in Node : phase[n] = "done" => n \notin recv[parent[n]]

====