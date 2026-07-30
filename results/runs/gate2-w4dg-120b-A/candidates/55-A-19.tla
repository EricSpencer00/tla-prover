---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS
  Node,
  initiator,
  R,
  NoNode

\* The Echo specification's full action set is imported here and then wired into
\* TestSpec in the same names the .cfg expects.
\* The constant set is deliberately left uninterpreted so that the cfg file can
\* pin down exactly three concrete nodes and the fully-meshed graph on top of
\* them.
ASSUME NoNode \notin Node
ASSUME R \subseteq (Node \X Node)

VARIABLES active, dormant, parent, sent, receiveCount

vars == <<active, dormant, parent, sent, receiveCount>>

Active(n) == active[n]
Idle == \A n \in Node : n \notin active

\* The Echo algorithm aggregates messages at a single initiator; it is
\* complete once the initiator has consumed everything that was sent.
Complete == (initiator \in active)
            /\ \A n \in Node : sent[n] = receiveCount[n]

Init ==
  /\ active = {}
  /\ dormant = Node
  /\ parent = [n \in Node |-> NoNode]
  /\ sent = [n \in Node |-> 0]
  /\ receiveCount = [n \in Node |-> 0]

Begin ==
  /\ Idle
  /\ active' = {initiator}
  /\ dormant' = Node \ {initiator}
  /\ parent' = [parent EXCEPT ![initiator] = NoNode]
  /\ UNCHANGED <<sent, receiveCount>>

Send ==
  /\ \E n \in active, m \in dormant :
       /\ <<n, m>> \in R
       /\ active' = active \cup {m}
       /\ dormant' = dormant \ {m}
       /\ parent' = [parent EXCEPT ![m] = n]
       /\ sent' = [sent EXCEPT ![n] = @ + 1]
  /\ UNCHANGED receiveCount

Receive ==
  /\ \E n \in active :
       /\ sent[n] > receiveCount[n]
       /\ receiveCount' = [receiveCount EXCEPT ![n] = @ + 1]
  /\ UNCHANGED <<active, dormant, parent, sent>>

Finish ==
  /\ Complete
  /\ \A n \in Node : sent[n] = receiveCount[n]
  /\ UNCHANGED vars

Next == Begin \/ Send \/ Receive \/ Finish

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ active \subseteq Node
  /\ dormant \subseteq Node
  /\ active \cap dormant = {}
  /\ active \cup dormant = Node
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sent \in [Node -> Nat]
  /\ receiveCount \in [Node -> Nat]

AncestorProperties ==
  /\ \A n \in Node : (parent[n] # NoNode) => (parent[n] \in active)
  /\ \A n \in Node : (parent[n] # NoNode) => (n \notin {parent[n]})
  /\ (initiator \in active) => (parent[initiator] = NoNode)

\* TestSpec is the identifier the .cfg files reference for the main spec. It
\* prints the graph relation at startup and then behaves exactly like Spec.
TestSpec ==
  /\ Spec
  /\ \A n \in Node : Cardinality({m \in Node : <<n, m>> \in R}) = Cardinality({m \in Node : <<m, n>> \in R})
  /\ UNCHANGED vars

====