---- MODULE MCEcho ----
EXTENDS Integers

\* Model-checking configuration: a concrete three-node fully-connected graph
\* for the Echo spanning-tree algorithm, with a deterministic initiator.
CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, notified, done, sent, border
vars == <<parent, notified, done, sent, border>>

Notified == {n \in Node : notified[n]}
HasChild(n) == \E m \in Node : parent[m] = n
IsAncestor(n) ==
  \E m \in Node :
    /\ n = m \/ n \in notified
    /\ (m # n => notified[m])
    /\ (\A c \in Node : parent[c] = n => IsAncestor(c))

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ notified \in [Node -> BOOLEAN]
  /\ done \in [Node -> BOOLEAN]
  /\ sent \in [Node \times Node -> BOOLEAN]
  /\ border \in [Node -> BOOLEAN]

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ notified = [n \in Node |-> FALSE]
  /\ done = [n \in Node |-> FALSE]
  /\ sent = [p \in Node \times Node |-> FALSE]
  /\ border = [n \in Node |-> TRUE]

Start ==
  /\ ~notified[initiator]
  /\ parent' = [parent EXCEPT ![initiator] = initiator]
  /\ notified' = [notified EXCEPT ![initiator] = TRUE]
  /\ UNCHANGED <<done, sent, border>>

\* Request a still-silent neighbour (the mesh means a requester is always
\* reachable from every silent node, so this cannot deadlock).
Request(n, m) ==
  /\ notified[n] /\ ~notified[m] /\ m \in R[n]
  /\ ~sent[n, m]
  /\ sent' = [sent EXCEPT ![n, m] = TRUE]
  /\ UNCHANGED <<parent, notified, done, border>>

Reply(m, n) ==
  /\ sent[n, m] /\ notified[n] /\ ~notified[m]
  /\ parent' = [parent EXCEPT ![m] = n]
  /\ notified' = [notified EXCEPT ![m] = TRUE]
  /\ sent' = [sent EXCEPT ![n, m] = FALSE]
  /\ UNCHANGED <<done, border>>

\* A notified node sends to a neighbour (whether or not it answered first).
GiveUp(n, m) ==
  /\ notified[n] /\ notified[m] /\ sent[n, m]
  /\ sent' = [sent EXCEPT ![n, m] = FALSE]
  /\ UNCHANGED <<parent, notified, done, border>>

\* The initiator's own active move; it needs no neighbour to grant it.
Echo(n) ==
  /\ notified[n] /\ ~done[n]
  /\ done' = [done EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<parent, notified, sent, border>>

Idle ==
  /\ \A n \in Node : notified[n] /\ done[n]
  /\ UNCHANGED vars

Next ==
  \/ Start
  \/ \E n, m \in Node : Request(n, m) \/ Reply(m, n) \/ GiveUp(n, m) \/ Echo(n)
  \/ Idle

AncestorProperties == (initiator # NoNode) /\ IsAncestor(initiator)

\* TestSpec: the variant the .cfg file drives, anchored at the Init state.
TestSpec == Init /\ [][Next]_vars
====