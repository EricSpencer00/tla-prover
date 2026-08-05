---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

\* Echo spanning tree, instantiated with a concrete three-node fully-meshed graph.
\* The module defines no extra state; it inherits all variables and actions
\* from the Echo specification and merely fixes the node set, the initiator,
\* and the symmetric, irreflexive edge relation.
CONSTANTS Node, initiator, R, NoNode

TypeOK ==
  /\ initiator \in Node
  /\ R \subseteq [a : Node, b : Node]
  /\ NoNode \notin Node

VARIABLES init, tree, parent, phase
vars == << init, tree, parent, phase >>

Init ==
  /\ init = initiator
  /\ tree = {}
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> "idle"]

SendEcho ==
  /\ \E n \in Node :
       /\ n # init
       /\ phase[n] = "idle"
       /\ [a |-> init, b |-> n] \in R
       /\ init \notin tree
       /\ tree' = tree \cup {[a |-> init, b |-> n]}
       /\ parent' = [parent EXCEPT ![n] = init]
       /\ phase' = [phase EXCEPT ![n] = "active"]
  /\ UNCHANGED init

Propagate ==
  /\ \E e \in tree :
       /\ phase[e.b] = "idle"
       /\ [a |-> e.b, b |-> e.a] \notin tree
       /\ tree' = tree \cup {[a |-> e.b, b |-> e.a]}
       /\ parent' = [parent EXCEPT ![e.b] = e.a]
       /\ phase' = [phase EXCEPT ![e.b] = "active"]
  /\ UNCHANGED init

Reply ==
  /\ \E n \in Node :
       /\ phase[n] = "active"
       /\ n # init
       /\ parent[n] \in Node
       /\ phase[parent[n]] # "idle"
       /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED << init, tree, parent >>

Finish ==
  /\ \A n \in Node : phase[n] = "done"
  /\ UNCHANGED vars

Next == SendEcho \/ Propagate \/ Reply \/ Finish

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(SendEcho)
  /\ WF_vars(Propagate)
  /\ WF_vars(Reply)

\* Safety invariants inherited from Echo: type-correctness and the tree
\* constraints (every non-initiator has an ancestor and there is no cycle).
TypeOKInv == TypeOK
AncestorProperties ==
  /\ \A n \in Node : n # init => init \in Reach(n)
  /\ \A n \in Node : n # init => ~(n \in Reach(n))

\* TestSpec adds a one-time print of the adjacency relation at startup, so
\* the model checker is not confused by a spec that appears to take no steps.
TestSpec ==
  /\ Spec
  /\ (Init /\ UNCHANGED vars) \/ Next

====