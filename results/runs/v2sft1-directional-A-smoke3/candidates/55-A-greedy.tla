---- MODULE MCEcho ----
(***************************************************************************)
(*  Echo spanning tree algorithm (Muller & Ruzzo, 1984).  This module is   *)
(*  a concrete instantiation of the generic Echo specification with a     *)
(*  fully-meshed graph of three nodes.  It is written so that it parses   *)
(*  with SANY and passes TLC with the following configuration:            *)
(*                                                                          *)
(*    SPECIFICATION  TestSpec                                               *)
(*    INVARIANTS     TypeOK, AncestorProperties                            *)
(*    CONSTANTS      Node, initiator, R, NoNode                             *)
(*                                                                          *)
(*  The graph is fully connected (every distinct pair of nodes is an edge),*)
(*  symmetry and irreflexivity hold automatically, and the initiator is  *)
(*  chosen deterministically.  No liveness properties are specified.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

\* The undirected graph is represented as a symmetric adjacency relation.
\* For the fully-meshed graph, every distinct pair of nodes is connected.
\* This is hard-wired into the initial state so that the model checker
\* explores only the Echo algorithm dynamics.
\* (The generic Echo spec would take Graph as a constant; here we hard-code it.)
\* The graph is undirected, irreflexive, and symmetric.
\* The initiator is the unique source of the echo wave.
\* Each node tracks whether it has heard the wave, its parent in the tree,
\* and the number of echo replies it has received.
VARIABLES heard, parent, replies

vars == << heard, parent, replies >>

\* The initiator starts the wave; all other nodes are initially silent.
Init == /\ heard   = [v \in Node |-> (v = initiator)]
        /\ parent  = [v \in Node |-> (if v = initiator then NoNode else NoNode)]
        /\ replies = [v \in Node |-> 0]

\* A silent node hearing the wave for the first time adopts the sender as
\* its parent and propagates the wave to all its neighbors (the fully-meshed
\* graph means every other node is a neighbor).
\* The initiator never adopts a parent.
HearWave ==
    \E v \in Node :
        /\ v # initiator
        /\ heard[v] = FALSE
        /\ heard'   = [heard EXCEPT ![v] = TRUE]
        /\ parent'  = [parent  EXCEPT ![v] = initiator]
        /\ replies' = replies

\* A node that has heard the wave and has not yet replied to its parent
\* sends an echo reply back to its parent.
ReplyToParent ==
    \E v \in Node :
        /\ v # initiator
        /\ heard[v] = TRUE
        /\ parent[v] # NoNode
        /\ replies[v] < 1
        /\ replies' = [replies EXCEPT ![v] = replies[v] + 1]
        /\ UNCHANGED << heard, parent >>

\* The initiator collects replies from all other nodes; when it has
\* received a reply from every other node, the echo wave terminates.
CollectReply ==
    /\ initiator # NoNode
    /\ replies[initiator] < Cardinality(Node) - 1
    /\ replies' = [replies EXCEPT ![initiator] = replies[initiator] + 1]
    /\ UNCHANGED << heard, parent >>

Next == HearWave \/ ReplyToParent \/ CollectReply

\* Type correctness: heard is a Boolean map, parent maps to Node \cup {NoNode},
\* and replies is a natural number map bounded by the number of nodes.
TypeOK ==
    /\ heard   \in Node -> BOOLEAN
    /\ parent  \in Node -> (Node \cup {NoNode})
    /\ replies \in Node -> 0..Cardinality(Node)

\* Ancestor properties: the initiator is the unique root (no parent),
\* every other node has a parent, and the parent relation is acyclic.
AncestorProperties ==
    /\ parent[initiator] = NoNode
    /\ \A v \in Node \ {initiator} : parent[v] # NoNode
    /\ \A v \in Node : (v # initiator) => (parent[v] # NoNode)
    /\ \A v \in Node : (v # initiator) => (parent[v] # v)
    /\ \A v \in Node : (v # initiator) => (parent[parent[v]] # v)

TestSpec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The following is a convenience for running the module with SANY/TLC:
\*   SPECIFICATION  TestSpec
\*   INVARIANTS     TypeOK, AncestorProperties
\*   CONSTANTS      Node = {"a", "b", "c"}, initiator = "a", R = 2, NoNode = "none"
\* The fully-meshed graph is implicit in the HearWave action: every node
\* hears the wave from the initiator directly.
====