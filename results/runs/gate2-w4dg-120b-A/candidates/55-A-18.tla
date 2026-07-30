---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

\* Complete set of all directed edges in the fully-meshed graph (the Echo
\* spec's edge relation is symmetric and irreflexive, so we pass it as an
\* undirected set of unordered pairs).
Edges == {e \in [Node \X Node] : e[1] # e[2]}

VARIABLES parent, done, pending

vars == <<parent, done, pending>>

Init ==
  /\ \A n \in Node : parent[n] = NoNode
  /\ \A n \in Node : done[n] = FALSE
  /\ \A n \in Node : pending[n] = FALSE

\* The initiator fires first and is the root of the spanning tree.
SendFromInitiator ==
  /\ ~done[initiator]
  /\ ~pending[initiator]
  /\ pending' = [pending EXCEPT ![initiator] = TRUE]
  /\ UNCHANGED <<parent, done>>

\* A node forwards to an adjacent node that is not its own parent.
Forward(m, n) ==
  /\ pending[m]
  /\ m # n
  /\ <<m, n>> \in Edges
  /\ ~done[n]
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ pending' = [pending EXCEPT ![m] = FALSE]
  /\ pending' = [pending EXCEPT ![n] = TRUE]
  /\ UNCHANGED done

\* A leaf node with no pending send marks itself done (becomes a leaf of the
\* spanning tree).
Terminate(n) ==
  /\ ~pending[n]
  /\ ~done[n]
  /\ (n = initiator \/ parent[n] # NoNode)
  /\ done' = [done EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, pending>>

Next ==
  \/ SendFromInitiator
  \/ \E m, n \in Node : Forward(m, n)
  \/ \E n \in Node : Terminate(n)

TestSpec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A n \in Node : parent[n] \in Node \cup {NoNode}
  /\ \A n \in Node : done[n] \in BOOLEAN
  /\ \A n \in Node : pending[n] \in BOOLEAN

Ancestor(n) == IF n = initiator THEN initiator ELSE parent[n]

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A n \in Node : parent[n] # n
  /\ \A n \in Node :
       (n # initiator /\ parent[n] # NoNode) => Ancestor(parent[n]) # n

====