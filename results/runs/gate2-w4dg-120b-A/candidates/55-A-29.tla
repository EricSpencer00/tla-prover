---- MODULE MCEcho ----
EXTENDS Integers

(* A model-checking configuration module for the Echo spanning tree algorithm,
   instantiated with a concrete three-node fully-connected graph.  It mirrors the
   Echo specification exactly in terms of state and actions; the only variation is
   the concrete graph and the deterministic initiator choice, which keep the
   state space finite for exhaustive checking.  The constant NoNode is a sentinel
   distinct from every node. *)

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES parent, acked, phase

vars == <<parent, acked, phase>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ acked \in [Node -> BOOLEAN]
  /\ phase \in [Node -> {"idle", "waiting", "done"}]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ acked = [n \in Node |-> FALSE]
  /\ phase = [n \in Node |-> "idle"]

Send(n, m) ==
  /\ n # m
  /\ {n, m} \subseteq R
  /\ phase[n] = "idle"
  /\ phase' = [phase EXCEPT ![n] = "waiting"]
  /\ UNCHANGED <<parent, acked>>

Echo(n, m) ==
  /\ n # m
  /\ {n, m} \subseteq R
  /\ phase[n] = "waiting"
  /\ phase[m] = "idle"
  /\ phase' = [phase EXCEPT ![m] = "waiting"]
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ UNCHANGED <<acked>>

Ack(n) ==
  /\ phase[n] = "waiting"
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ acked' = [acked EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent>>

IdleStep == /\ \A n \in Node : phase[n] = "done" /\ UNCHANGED vars

Next ==
  \/ \E n, m \in Node : Send(n, m)
  \/ \E n, m \in Node : Echo(n, m)
  \/ \E n \in Node : Ack(n)
  \/ IdleStep

Spec == Init /\ [][Next]_vars

AncestorProperties ==
  /\ \A n \in Node : n # initiator => (parent[n] # NoNode /\ parent[n] \in Node)
  /\ \A n \in Node : (parent[n] # NoNode /\ parent[parent[n]] # NoNode) => parent[parent[n]] # n
  /\ \A n \in Node : parent[n] = initiator => n # initiator

TestSpec == Spec

====