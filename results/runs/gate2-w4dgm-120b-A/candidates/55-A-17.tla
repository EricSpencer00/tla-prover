---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node
ASSUME NoNode \notin Node

\* The underlying Echo specification (Init/Next) is fully parametric in the
\* graph; this module supplies a concrete, fully-meshed three-node graph.
\* A test variant of the spec prints the edge set for debugging.

VARIABLES parent, active, done, joinEpoch, phase

vars == <<parent, active, done, joinEpoch, phase>>

Neighbors(x) == {y \in Node : y # x}

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ active = {initiator}
  /\ done = {}
  /\ joinEpoch = [n \in Node |-> 0]
  /\ phase = "echoing"

\* A node forwards the echo to each neighbor it has not yet joined.
Echo(n) ==
  /\ n \in active
  /\ n \notin done
  /\ LET newActive == {m \in Neighbors(n) : parent[m] = NoNode}
     IN /\ parent' = [parent EXCEPT ![m] = n : m \in newActive]
        /\ active' = active \cup newActive
  /\ UNCHANGED <<done, joinEpoch, phase>>

\* A leaf records its own echo and stops forwarding.
LeafEcho(n) ==
  /\ n \in active
  /\ n \notin done
  /\ Neighbors(n) \subseteq active
  /\ done' = done \cup {n}
  /\ UNCHANGED <<parent, active, joinEpoch, phase>>

\* When every node is done, the echo terminates.
Terminate ==
  /\ active = Node
  /\ done = Node
  /\ phase' = "terminated"
  /\ UNCHANGED <<parent, active, done, joinEpoch>>

\* A finished node may rejoin the active frontier in a fresh epoch, and its
\* downstream descendants follow it so the tree stays connected.
Rejoin(n) ==
  /\ n \in done
  /\ joinEpoch' = [joinEpoch EXCEPT ![n] = joinEpoch[n] + 1]
  /\ active' = active \cup {n}
  /\ done' = done \ {n}
  /\ UNCHANGED <<parent, phase>>

\* Test variant: print the graph (full mesh) once at startup and never again.
PrintGraph ==
  /\ phase = "echoing"
  /\ Cardinality(active) = 1
  /\ \A a \in active, b \in Node : (a # b) => b \in Neighbors(a)
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Node : Echo(n)
  \/ \E n \in Node : LeafEcho(n)
  \/ Terminate
  \/ \E n \in Node : Rejoin(n)
  \/ PrintGraph

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ active \subseteq Node
  /\ done \subseteq Node
  /\ joinEpoch \in [Node -> 0..1]
  /\ phase \in {"echoing", "terminated"}

AncestorProperties ==
  /\ (done = {}) \/ (initiator \in done /\ Cardinality(active) > 0)
  /\ \A n \in Node : (n \in done /\ n # initiator) => parent[n] \in done
  /\ \A n \in Node : (n \in done /\ parent[n] # NoNode) => parent[n] # n
  /\ \A n \in Node : (n \in done /\ parent[n] # NoNode) => (parent[n] \in done)

\* The .cfg file injects concrete finite sets for the quantified identifiers,
\* so the spec itself stays parametric in how many nodes there are.
N1 == Node
I1 == initiator
R1 == R

TestSpec == Spec
====