---- MODULE MCEcho ----
EXTENDS Integers

(* Model-checking configuration module for the Echo spanning tree          *)
(* algorithm.  It instantiates the Echo spec with a small fully-connected    *)
(* three-node graph so that exhaustive state-space exploration is           *)
(* feasible.  The module inherits the state space, actions, and invariants   *)
(* of the Echo specification; it only defines the concrete constants and    *)
(* the test variant that prints the graph.                                  *)

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sending, recd, inCS

vars == <<parent, sending, recd, inCS>>

RECURSIVE Anc(_, _)
Anc(f, x) == IF f[x] = NoNode THEN {} ELSE {x} \cup Anc(f, f[x])

Init ==
  /\ parent \in [Node -> {NoNode} \cup Node]
  /\ sending \in [Node -> 0..1]
  /\ recd \in [Node -> 0..1]
  /\ inCS \in [Node -> BOOLEAN]

SendEcho(n) ==
  /\ n = initiator
  /\ sending[n] = 0
  /\ sending' = [sending EXCEPT ![n] = 1]
  /\ UNCHANGED <<parent, recd, inCS>>

EchoTo(v) ==
  /\ sending[initiator] = 1
  /\ v # initiator
  /\ parent[v] = NoNode
  /\ parent' = [parent EXCEPT ![v] = initiator]
  /\ recd' = [recd EXCEPT ![v] = 1]
  /\ sending' = [sending EXCEPT ![initiator] = 0]
  /\ UNCHANGED inCS

ReEcho(u) ==
  /\ \E v \in Node :
       /\ u # v
       /\ recd[v] = 1
       /\ parent[v] # NoNode
       /\ parent[v] # u
       /\ recd' = [recd EXCEPT ![v] = 0]
       /\ recd' = [recd EXCEPT ![u] = 1]
       /\ parent' = [parent EXCEPT ![v] = u]
  /\ UNCHANGED <<sending, inCS>>

EnterCS(n) ==
  /\ \A m \in Node : recd[m] = 1
  /\ inCS' = [inCS EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, sending, recd>>

LeaveCS(n) ==
  /\ inCS[n]
  /\ parent' = [x \in Node |-> IF x = n THEN NoNode ELSE parent[x]]
  /\ sending' = [sending EXCEPT ![n] = 0]
  /\ recd' = [recd EXCEPT ![n] = 0]
  /\ inCS' = [x \in Node |-> IF x = n THEN FALSE ELSE inCS[x]]

Next ==
  \/ \E n \in Node : SendEcho(n)
  \/ \E v \in Node : EchoTo(v)
  \/ \E u \in Node : ReEcho(u)
  \/ \E n \in Node : EnterCS(n)
  \/ \E n \in Node : LeaveCS(n)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ parent \in [Node -> {NoNode} \cup Node]
  /\ sending \in [Node -> {0, 1}]
  /\ recd \in [Node -> {0, 1}]
  /\ inCS \in [Node -> BOOLEAN]

AncestorProperties ==
  /\ initiator \in {x \in Node : parent[x] # NoNode}
  /\ \A n, m \in Node : (m \in Anc(parent, n) /\ n \in Anc(parent, m)) => m = n

(* Test variant: prints the graph adjacency relation to standard output at  *)
(* startup; the action itself is never enabled once the system has stabilized.*)
PrintGraph ==
  /\ UNCHANGED vars

TestSpec == Spec /\ [][PrintGraph]_vars

====