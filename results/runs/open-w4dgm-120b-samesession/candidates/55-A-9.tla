---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

\* An Echo spanning tree started by 'initiator' on a fully connected
\* three-node graph; Next/Init/Idle are the Echo actions plus a test
\* print of the adjacency relation. InitEager/InitQuiet choose the
\* initiator by a deterministic parity rule so the graph is fully
\* explored from a fixed start; the test printer is guarded so the
\* model never prints on an infinite run.

VARIABLES mode, state, acked, parent, reply, active

vars == <<mode, state, acked, parent, reply, active>>

Nodes == Node
Edges == {<<i, j>> : i \in Nodes, j \in Nodes : i # j}

TypeOK ==
  /\ mode \in {"idle", "echo", "done", "test"}
  /\ state \in [Nodes -> {"fresh", "asked", "sent", "replied"}]
  /\ acked \subseteq Nodes
  /\ parent \in [Nodes -> Nodes \cup {NoNode}]
  /\ reply \in [Nodes -> {"none", "ok"}]
  /\ active \in Nodes \cup {NoNode}

InitEager ==
  /\ mode = "idle"
  /\ mode' = "echo"
  /\ state' = [n \in Nodes |-> IF n = initiator THEN "asked" ELSE "fresh"]
  /\ acked' = {}
  /\ parent' = [n \in Nodes |-> NoNode]
  /\ reply' = [n \in Nodes |-> "none"]
  /\ active' = initiator

InitQuiet ==
  /\ mode = "idle"
  /\ mode' = "echo"
  /\ state' = [n \in Nodes |-> IF n = I1 THEN "asked" ELSE "fresh"]
  /\ acked' = {}
  /\ parent' = [n \in Nodes |-> NoNode]
  /\ reply' = [n \in Nodes |-> "none"]
  /\ active' = I1

Send ==
  /\ mode = "echo"
  /\ \E s \in Nodes, d \in Nodes :
       /\ state[s] = "asked"
       /\ state' = [state EXCEPT ![s] = "sent"]
       /\ parent' = [parent EXCEPT ![d] = s]
       /\ state' = [state EXCEPT ![d] = "asked"]
  /\ UNCHANGED <<mode, acked, reply, active>>

Reply ==
  /\ mode = "echo"
  /\ \E d \in Nodes :
       /\ state[d] = "asked"
       /\ parent[d] # NoNode
       /\ state' = [state EXCEPT ![d] = "replied"]
       /\ reply' = [reply EXCEPT ![d] = "ok"]
       /\ acked' = acked \cup {d}
  /\ UNCHANGED <<mode, parent, active>>

\* A quiet leaf that never shouted: its parent answered it directly.
Quiesce ==
  /\ mode = "echo"
  /\ \E d \in Nodes :
       /\ state[d] = "asked"
       /\ parent[d] # NoNode
       /\ ~\E s \in Nodes : state[s] = "sent" /\ parent[s] = d
       /\ state' = [state EXCEPT ![d] = "replied"]
       /\ reply' = [reply EXCEPT ![d] = "ok"]
       /\ acked' = acked \cup {d}
  /\ UNCHANGED <<mode, parent, active>>

PrintGraph ==
  /\ mode = "idle"
  /\ \E e \in Edges : e # <<NoNode, NoNode>>
  /\ mode' = "test"
  /\ UNCHANGED <<state, acked, parent, reply, active>>

AllDone == mode = "echo" /\ \A n \in Nodes : state[n] = "replied"

Done ==
  /\ AllDone
  /\ mode' = "done"
  /\ UNCHANGED <<state, acked, parent, reply, active>>

Idle ==
  /\ mode = "done"
  /\ UNCHANGED vars

Next ==
  \/ InitEager \/ InitQuiet \/ Send \/ Reply
  \/ Quiesce \/ PrintGraph \/ Done \/ Idle

Init == InitEager

Spec == Init /\ [][Next]_vars /\ WF_vars(Reply) /\ WF_vars(Quiesce)

\* An initiator that never replied would leave a node acknowledged by
\* nobody; the ancestor test would then flag the initiator as missing.
AncestorProperties ==
  /\ \A n \in Nodes : n # initiator => parent[n] # NoNode
  /\ \A n \in Nodes : n # initiator => n \in acked
  /\ \A n \in Nodes : initiator \in {m \in Nodes : m # NoNode /\ parent[m] = n} ~> (n = initiator)

TestSpec == Spec /\ InitQuiet

====