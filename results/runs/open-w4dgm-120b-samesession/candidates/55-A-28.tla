---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

(* A model-checking configuration module for the Echo spanning tree        *)
(* algorithm.  It reuses the Echo specification (type state, actions, and    *)
(* safety properties) and instantiates it with a three-node fully-meshed    *)
(* graph, which is small enough for exhaustive checking.  An alternative    *)
(* graph definition (commented out) shows how a nondeterministic connected  *)
(* graph over the same node set would be expressed.                         *)

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, echoing, active, haveEcho, acked

vars == <<parent, echoing, active, haveEcho, acked>>

RECURSIVE Reachable(_)
Reachable(n) ==
  IF n = initiator THEN {}
  ELSE LET pa == parent[n] IN IF pa = NoNode THEN {} ELSE {pa} \cup Reachable(pa)

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ echoing \in [Node -> BOOLEAN]
  /\ active \in [Node -> BOOLEAN]
  /\ haveEcho \in [Node -> BOOLEAN]
  /\ acked \in [Node -> SUBSET R]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ echoing = [n \in Node |-> FALSE]
  /\ active = [n \in Node |-> FALSE]
  /\ haveEcho = [n \in Node |-> FALSE]
  /\ acked = [n \in Node |-> {}]

Reply(e, n) ==
  /\ active[n]
  /\ ~acked[n]
  /\ acked' = [acked EXCEPT ![n] = acked[n] \cup {e}]
  /\ echoing' = IF echoing[n] /\ n # initiator THEN [echoing EXCEPT ![n] = @] ELSE echoing
  /\ UNCHANGED <<parent, active, haveEcho>>

ReceiveEcho(n) ==
  /\ ~haveEcho[n]
  /\ \E e \in acked[n] : haveEcho' = [haveEcho EXCEPT ![n] = @]
  /\ UNCHANGED <<parent, echoing, active, acked>>

SendEcho(n, m) ==
  /\ n # m
  /\ echoing[n]
  /\ ~active[m]
  /\ parent[m] = NoNode
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ echoing' = [echoing EXCEPT ![n] = @, ![m] = TRUE]
  /\ active' = [active EXCEPT ![m] = TRUE]
  /\ UNCHANGED <<haveEcho, acked>>

StartEcho(n) ==
  /\ n = initiator
  /\ ~echoing[n]
  /\ echoing' = [echoing EXCEPT ![n] = TRUE]
  /\ active' = [active EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, haveEcho, acked>>

Done == UNCHANGED vars

Next ==
  \/ \E e \in R, n \in Node : Reply(e, n)
  \/ \E n \in Node : ReceiveEcho(n)
  \/ \E n \in Node, m \in Node : SendEcho(n, m)
  \/ \E n \in Node : StartEcho(n)
  \/ Done

(* The variant that prints the graph adjacency relation at startup.  The  *)
(* graph here is fully meshed; the alternative (commented out) definition is *)
(* the nondeterministic connected-graph version the .cfg may substitute.    *)
TestSpec ==
  /\ \E e \in R, n \in Node : Reply(e, n)
  /\ \E n \in Node : ReceiveEcho(n)
  /\ \E n \in Node, m \in Node : SendEcho(n, m)
  /\ \E n \in Node : StartEcho(n)
  /\ UNCHANGED vars

Spec == TestSpec

AncestorProperties ==
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode /\ initiator \in Reachable(n))
  /\ \A n \in Node : parent[n] # NoNode => initiator \notin Reachable(parent[n])

====