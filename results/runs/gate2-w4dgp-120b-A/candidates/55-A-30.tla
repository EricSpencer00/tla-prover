---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

\* Echo algorithm: an initiator floods a find request, nodes forward it to
\* neighbors, and the request aggregates back as an ack up a spanning tree.
\* This module configures the base Echo model for a concrete three-node
\* fully-connected graph, and adds TestSpec which prints the graph at startup.
\* The safety properties (type-correctness, ancestor tree) are those of Echo.

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, phase, seen, recvBy

vars == <<parent, phase, seen, recvBy>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "flooding", "witnessed", "done"}]
  /\ seen \subseteq (Node \X Node)
  /\ recvBy \in [Node -> Node \cup {NoNode}]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> IF n = initiator THEN "flooding" ELSE "idle"]
  /\ seen = {}
  /\ recvBy = [n \in Node |-> NoNode]

\* Flood: an idle node receives a find request from a neighbor and records
\* that neighbor as its parent in the spanning tree.
Flood(m, n) ==
  /\ phase[n] = "idle"
  /\ <<m, n>> \in R
  /\ n # initiator
  /\ phase' = [phase EXCEPT ![n] = "flooding"]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ seen' = seen \cup {<<m, n>>}
  /\ UNCHANGED <<recvBy>>

\* Witness: the initiator (or any node that has its find request returning
\* to itself) records who finally sent it and becomes a witness of the echo.
Witness ==
  /\ phase[initiator] = "flooding"
  /\ recvBy[initiator] = NoNode
  /\ recvBy' = [recvBy EXCEPT ![initiator] = parent[initiator]]
  /\ phase' = [phase EXCEPT ![initiator] = "witnessed"]
  /\ UNCHANGED <<parent, seen>>

\* Ack: a node that is flooding forwards its find request back to its parent;
\* this is the echo aggregating up the spanning tree.
Ack(n) ==
  /\ phase[n] = "flooding"
  /\ parent[n] # NoNode
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ recvBy' = [recvBy EXCEPT ![parent[n]] = n]
  /\ UNCHANGED <<parent, seen>>

\* Done: a node that is already a witness or done stays done.
Done(n) ==
  /\ phase[n] \in {"witnessed", "done"}
  /\ UNCHANGED vars

Next ==
  \/ \E m \in Node, n \in Node : Flood(m, n)
  \/ \E n \in Node : Ack(n)
  \/ \E n \in Node : Done(n)
  \/ Witness

Spec == Init /\ [][Next]_vars

\* The spanning tree formed by the find request is a rooted tree: the
\* initiator reaches every other node, and an ack back to the initiator
\* would be the final aggregation step of the spanning tree.
AncestorProperties ==
  /\ \A n \in Node : (phase[n] # "idle") => (parent[n] # NoNode => parent[n] # n)
  /\ \A n \in Node : (phase[n] = "done") => (parent[n] # NoNode => phase[parent[n]] = "done")

\* TestSpec is a variant that, instead of checking a property, prints the
\* graph adjacency relation once at startup. Handy for debugging the binding
\* of the constants in the .cfg when re-running with a different graph shape.
TestSpec ==
  /\ Spec
  /\ (UNCHANGED vars)
  /\ (IF \A n \in Node : parent[n] = NoNode /\ phase[n] = "idle"
        THEN (PrintT("\nAdjacency relation R: "); PrintT(R); PrintT("\n")) /\ TRUE
        ELSE TRUE)

====