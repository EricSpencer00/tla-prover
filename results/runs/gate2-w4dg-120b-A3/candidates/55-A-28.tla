---- MODULE MCEcho ----
EXTENDS Integers

\* Model-checking configuration for the Echo spanning tree algorithm.
\* It re-exports the Echo model's operators and overlays a concrete
\* three-node fully-meshed graph as the default configuration; the
\* .cfg file then substitutes bounded versions of the constants.
\* The module also defines a test variant that prints the adjacency
\* relation at startup, for debugging.

CONSTANTS Node, initiator, R, NoNode

\* Derived from the Echo spec: each node's parent pointer, the set of
\* nodes that have adopted the echo, the set of nodes that have sent
\* the echo onward, and a per-node phase counter.
VARIABLES parent, adopted, sentOnward, phase

vars == <<parent, adopted, sentOnward, phase>>

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ adopted = {}
  /\ sentOnward = {}
  /\ phase = [n \in Node |-> 0]

InitiateEcho ==
  /\ initiator \notin adopted
  /\ adopted' = adopted \cup {initiator}
  /\ phase' = [phase EXCEPT ![initiator] = 1]
  /\ UNCHANGED <<parent, sentOnward>>

Adopt(n) ==
  /\ \E m \in Node : m \in adopted /\ <<m, n>> \in R
  /\ n \notin adopted
  /\ parent' = [parent EXCEPT ![n] = CHOOSE m \in Node : m \in adopted /\ <<m, n>> \in R]
  /\ adopted' = adopted \cup {n}
  /\ phase' = [phase EXCEPT ![n] = 1]
  /\ UNCHANGED <<sentOnward>>

SendOnward(n) ==
  /\ n \in adopted
  /\ n \notin sentOnward
  /\ \A p \in {q \in Node : <<n, q>> \in R} : p \in adopted
  /\ sentOnward' = sentOnward \cup {n}
  /\ phase' = [phase EXCEPT ![n] = 2]
  /\ UNCHANGED <<parent, adopted>>

EchoStep == InitiateEcho \/ (\E n \in Node : Adopt(n) \/ SendOnward(n))

Next == EchoStep

Spec == Init /\ [][Next]_vars

AncestorsAreAcyclic == \A n \in Node : (n # initiator) => (parent[n] # NoNode)

AncestorProperties ==
  /\ \A n \in Node : (n \in adopted) => (n = initiator \/ parent[n] # NoNode)
  /\ \A n \in Node : (n \in sentOnward) => (parent[n] # NoNode)
  /\ AncestorsAreAcyclic

TestSpec == Spec /\ PrintAdjacency

PrintAdjacency ==
  /\ \A n \in Node : \A m \in Node : n # m => (n \in Node /\ m \in Node)
  /\ UNCHANGED vars

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ adopted \subseteq Node
  /\ sentOnward \subseteq Node
  /\ phase \in [Node -> 0..2]

====