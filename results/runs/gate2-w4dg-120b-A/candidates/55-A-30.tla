---- MODULE MCEcho ----
EXTENDS Integers

(*  This module configures the Echo spanning-tree specification for model   *)
(*  checking on a tiny fully-connected three-node graph.  The Echo spec     *)
(*  refines spanning-tree construction with a single initiator node that    *)
(*  aggregates a convergecast.  No new actions are added here; what we add   *)
(*  are the concrete constants and the test variant that prints the graph.   *)

(*  Nodes of the graph.  All of these identifiers are duplicated in the      *)
(*  Echo spec (the mapping from a node to its parent in the spanning tree),   *)
(*  so they must all be declared here for the reference configuration.        *)
Node == {"v1", "v2", "v3"}

(*  The initiator is picked deterministically so that the model is finite    *)
(*  and fully covered -- a nondeterministic initiator would explode the      *)
(*  reachable state space for this tiny graph.                               *)
initiator == "v1"

(*  The edge relation.  For a fully-meshed graph every distinct pair of     *)
(*  nodes is a bidirectional edge.  The Echo spec expects a symmetric,       *)
(*  irreflexive relation, so we model both directions explicitly.             *)
R == { <<x, y>> : x \in Node /\ y \in Node /\ x # y }

(*  Sentinel for the "no parent" value in the spanning tree.  The Echo spec  *)
(*  treats this as a model value distinct from all nodes.                     *)
NoNode == "none"

VARIABLES parent, done, initPhase, acked

vars == <<parent, done, initPhase, acked>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ done \in [Node -> BOOLEAN]
  /\ initPhase \in BOOLEAN
  /\ acked \in [Node -> BOOLEAN]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ done = [n \in Node |-> FALSE]
  /\ initPhase = TRUE
  /\ acked = [n \in Node |-> FALSE]

Initialize(n) ==
  /\ initPhase
  /\ n = initiator
  /\ ~done[n]
  /\ parent' = [parent EXCEPT ![n] = n]
  /\ initPhase' = FALSE
  /\ UNCHANGED <<done, acked>>

SendParent(m, n) ==
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ UNCHANGED <<done, initPhase, acked>>

Receive(n) ==
  /\ parent[n] # NoNode
  /\ ~acked[n]
  /\ acked' = [acked EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, done, initPhase>>

Complete(n) ==
  /\ acked[n]
  /\ ~done[n]
  /\ done' = [done EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, initPhase, acked>>

Next ==
  \/ \E n \in Node : Initialize(n)
  \/ \E m, n \in Node : SendParent(m, n)
  \/ \E n \in Node : Receive(n)
  \/ \E n \in Node : Complete(n)

Spec == Init /\ [][Next]_vars

\*  A small test variant: print the graph's adjacency relation to standard    *
\*  output at model-check time.  The Echo spec itself needs no new operators. *
PrintGraph ==
  /\ LET EdgeCount == Cardinality(R)
     IN IF EdgeCount = 0
        THEN UNCHANGED vars
        ELSE
          /\ Printf("Model graph: %d edges, %d nodes", EdgeCount, Cardinality(Node))
          /\ UNCHANGED vars

TestSpec == Spec /\ PrintGraph

Ancestor(n) ==
  IF parent[n] = NoNode \/ parent[n] = n
  THEN {}
  ELSE {parent[n]} \cup Ancestor(parent[n])

AncestorProperties ==
  /\ (parent[initiator] = initiator) \/ (parent[initiator] = NoNode)
  /\ \A n \in Node : n # initiator => parent[n] \in Node \cup {NoNode}
  /\ \A n \in Node : n # initiator => (parent[n] = NoNode) \/ (n \notin Ancestor(n))

====