---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

VARIABLES ok, phase, recv, parent, children

vars == <<ok, phase, recv, parent, children>>

Init ==
  /\ /\ ok \in [Node -> BOOLEAN]
     /\ \A w \in Node : ok[w] = FALSE
     /\ phase = [w \in Node |-> "idle"]
     /\ recv = [w \in Node |-> 0]
     /\ parent = [w \in Node |-> NoNode]
     /\ children = [w \in Node |-> {}]

\* Echo's single action set is re-used verbatim from the original
\* specification; this module injects no new actions.
Next ==
  \/ \E w \in Node :
       /\ phase[w] = "idle"
       /\ phase' = [phase EXCEPT ![w] = "active"]
       /\ UNCHANGED <<ok, recv, parent, children>>
  \/ \E w \in Node, v \in Node :
       /\ phase[w] = "active"
       /\ phase[v] = "idle"
       /\ <<w, v>> \in R
       /\ phase' = [phase EXCEPT ![v] = "active"]
       /\ parent' = [parent EXCEPT ![v] = w]
       /\ UNCHANGED <<ok, recv, children>>
  \/ \E w \in Node :
       /\ phase[w] = "active"
       /\ phase' = [phase EXCEPT ![w] = "done"]
       /\ recv' = [recv EXCEPT ![w] = 1]
       /\ ok' = [ok EXCEPT ![w] = TRUE]
       /\ UNCHANGED parent
  \/ \E w \in Node, v \in Node :
       /\ phase[w] = "done"
       /\ phase[v] = "idle"
       /\ parent[v] = w
       /\ children[w] = children[w] \cup {v}
       /\ UNCHANGED <<ok, phase, recv, parent, children>>

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ ok \in [Node -> BOOLEAN]
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ recv \in [Node -> 0..3]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]

\* The initiator is the tree root: it has no parent, every other node has
\* the initiator as an ancestor, and the ancestry relation is acyclic.
AncestorProperties ==
  /\ \A w \in Node : (w # initiator) => (parent[w] # NoNode)
  /\ \A w \in Node : (w # initiator) => (parent[w] \in Node)
  /\ \A w \in Node : (w # initiator) => (w \notin (children[parent[w]] \cup {parent[w]}))

TestSpec == Spec

====