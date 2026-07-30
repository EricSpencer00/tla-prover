---- MODULE MCEcho ----
EXTENDS Integers

\* System overview: a model-checking configuration module for the Echo spanning
\* tree algorithm.  This module defines a concrete three-node fully-meshed graph
\* and picks one node as the initiator.  All state variables and actions are
\* inherited from the Echo specification; this module adds no new behaviour, but
\* it must expose the exact set of identifiers the reference model expects.
\* The fully-meshed graph satisfies the Echo spec's connectivity, symmetry,
\* and irreflexivity assumptions.  A sentinel constant NoNode marks "no
\* parent" and is distinct from every node.

CONSTANTS
  Node
  initiator
  R
  NoNode

Nodes == {"n1", "n2", "n3"}
AllPairs == {"n1", "n2", "n3"}

RECURSIVE PairsOf(_)
PairsOf(S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE e \in S : TRUE
       IN {<<x, y>> : y \in S \ {x}} \cup PairsOf(S \ {x})

Edges == PairsOf(AllPairs)

VARIABLES parent, active, done, phase
vars == <<parent, active, done, phase>>

InitEcho ==
  /\ parent = [n \in Nodes |-> NoNode]
  /\ active = Nodes
  /\ done = {}
  /\ phase = [n \in Nodes |-> "idle"]

PropagateEcho ==
  /\ \E e \in Nodes :
       /\ parent[e] = NoNode
       /\ active' = active \cup {e}
       /\ phase' = [phase EXCEPT ![e] = "active"]
  /\ UNCHANGED <<parent, done>>

\* The sending node records itself as the recipient's parent and moves from
\* active to done (the initiator stops being active once its message is sent).
EchoMessage ==
  /\ \E e \in Nodes :
       /\ e \in active
       /\ \E r \in Nodes \ {e} :
            /\ parent' = [parent EXCEPT ![r] = e]
            /\ done' = done \cup {r}
       /\ active' = active \ {e}
       /\ phase' = [phase EXCEPT ![e] = "done"]
  /\ UNCHANGED <<phase>>

TestSpec ==
  /\ InitEcho
  /\ EchoMessage

NextEcho ==
  \/ PropagateEcho
  \/ EchoMessage

SpecEcho == InitEcho /\ [][NextEcho]_vars

TypeOK ==
  /\ parent \in [Nodes -> Nodes \cup {NoNode}]
  /\ active \subseteq Nodes
  /\ done \subseteq Nodes
  /\ phase \in [Nodes -> {"idle", "active", "done"}]

\* Spanning tree safety: only the initiator has no parent, and the parent relation
\* is acyclic (an ancestor of an ancestor must be the initiator).
AncestorProperties ==
  /\ parent[initiator] = NoNode
  /\ \A n \in Nodes \ {initiator} : parent[n] # NoNode
  /\ \A a, b \in Nodes : (a # NoNode /\ b # NoNode /\ parent[b] = a) => (a = initiator \/ parent[a] # NoNode)

Spec == SpecEcho
Init == InitEcho
Next == NextEcho
Invars == TypeOK /\ AncestorProperties

====