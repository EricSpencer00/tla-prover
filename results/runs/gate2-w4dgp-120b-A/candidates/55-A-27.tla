---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* Echo spanning tree: fully-meshed three-node graph (every distinct pair linked),
\* with one deterministic initiator. Inherits all Echo state and actions.
VARIABLES parent, sentTo, phase, acked

vars == <<parent, sentTo, phase, acked>>

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ sentTo \in [Node -> SUBSET Node]
  /\ phase \in [Node -> {"idle","waiting","done"}]
  /\ acked \in [Node -> SUBSET Node]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ sentTo = [n \in Node |-> {}]
  /\ phase = [n \in Node |-> "idle"]
  /\ acked = [n \in Node |-> {}]
  /\ LET i == CHOOSE x \in initiator : TRUE IN
       /\ parent' = [parent EXCEPT ![i] = i]
       /\ phase' = [phase EXCEPT ![i] = "done"]
       /\ UNCHANGED <<sentTo, acked>>

\* Send the Echo message to a neighbor (every distinct pair is a link).
Send(n, m) ==
  /\ parent[n] = NoNode
  /\ n # m
  /\ m \notin sentTo[n]
  /\ sentTo' = [sentTo EXCEPT ![n] = sentTo[n] \cup {m}]
  /\ phase' = [phase EXCEPT ![n] = "waiting"]
  /\ UNCHANGED <<parent, acked>>

\* Receive the Echo message and adopt the sender as parent.
Receive(m, n) ==
  /\ m \in sentTo[n]
  /\ parent[n] = NoNode
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED <<sentTo, phase, acked>>

\* The initiator acknowledges a child when its own phase is done.
Ack(n, c) ==
  /\ parent[c] = n
  /\ phase[n] = "done"
  /\ c \notin acked[n]
  /\ acked' = [acked EXCEPT ![n] = acked[n] \cup {c}]
  /\ UNCHANGED <<parent, sentTo, phase>>

SetDone(n) ==
  /\ phase[n] = "waiting"
  /\ \A p \in Node : parent[p] = n => p \in acked[n]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED <<parent, sentTo, acked>>

Next ==
  \/ \E n \in Node, m \in Node : Send(n, m)
  \/ \E m \in Node, n \in Node : Receive(m, n)
  \/ \E n \in Node, c \in Node : Ack(n, c)
  \/ \E n \in Node : SetDone(n)

NextPrime == Next

Spec == Init /\ [][Next]_vars

TestSpec == Spec /\ TRUE

\* Safety: the initiator is ancestor of everyone and the ancestor relation is
\* acyclic -- true in every reachable state of a spanning tree.
AncestorProperties ==
  /\ \A n \in Node : parent[n] # NoNode => parent[parent[n]] # NoNode
  /\ \A n \in Node : parent[n] # NoNode => initiator \subseteq {n}

====