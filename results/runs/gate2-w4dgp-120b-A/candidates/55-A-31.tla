---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, state, inTree, sentEcho

vars == <<parent, state, inTree, sentEcho>>

\* This module is a model-checking wrapper for the Echo spanning tree
\* algorithm.  It inherits the full Echo action set and adds a test
\* variant that prints the (concrete, fully-meshed) graph at startup.
\* The safety property it shares with Echo is structural/spanning-tree
\* soundness, not an application-level correctness condition -- echo
\* finishes with every node in the tree, with no cycles in the
\* parent/ancestor relation.

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ state = [n \in Node |-> "idle"]
  /\ inTree = {initiator}
  /\ sentEcho = {}

Explore(n) ==
  /\ state[n] = "idle"
  /\ \E m \in Node :
       /\ n \in R[m]
       /\ state[m] = "idle"
       /\ m # n
       /\ parent' = [parent EXCEPT ![n] = m]
  /\ state' = [state EXCEPT ![n] = "explored"]
  /\ inTree' = inTree \cup {n}
  /\ UNCHANGED sentEcho

Echo(n, m) ==
  /\ state[n] = "explored"
  /\ m \in R[n]
  /\ <<n, m>> \notin sentEcho
  /\ sentEcho' = sentEcho \cup {<<n, m>>}
  /\ UNCHANGED <<parent, state, inTree>>

EchoStep == \E n \in Node, m \in Node : Echo(n, m)

Done == \A n \in Node : state[n] = "explored"

Quit == Done /\ UNCHANGED vars

Next == (\E n \in Node : Explore(n)) \/ EchoStep \/ Quit

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ state \in [Node -> {"idle", "explored"}]
  /\ sentEcho \subseteq (Node \X Node)
  /\ inTree \subseteq Node

Ancestors(n) == { m \in Node : (m = n) \/ (parent[n] # NoNode /\ m \in Ancestors(parent[n])) }

AncestorProperties ==
  /\ initiator \in inTree
  /\ \A n \in Node : (n \in inTree) => (initiator \in Ancestors(n))
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[n] \in inTree)

InitPrint ==
  LET pr(s) == IF s = {} THEN "{}" ELSE "{" /\ CHOOSE x \in s : TRUE /\ "}" /\ pr(s \ {x})
  IN /\ UNCHANGED vars
     /\ pr(R) # "{}"
     /\ pr(R) # pr([n \in Node |-> {n}])

Spec == Init /\ [][Next]_vars
TestSpec == Spec /\ InitPrint

====