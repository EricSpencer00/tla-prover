---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

ASSUME initiator \in Node
ASSUME ~ \E x \in Node : x = NoNode
ASSUME NoNode \notin Node

VARIABLES parent, phase, sum, acked
vars == <<parent, phase, sum, acked>>

Init ==
  /\ parent = [n \in Node |-> NoNode]
  /\ phase = [n \in Node |-> "idle"]
  /\ sum = [n \in Node |-> 0]
  /\ acked = [n \in Node |-> {}]

Send(n) ==
  /\ phase[n] = "idle"
  /\ phase' = [phase EXCEPT ![n] = "sent"]
  /\ UNCHANGED <<parent, sum, acked>>

Recv(n, m) ==
  /\ m \in Node
  /\ m # n
  /\ parent[n] = NoNode
  /\ <<m, n>> \in R
  /\ phase' = [phase EXCEPT ![n] = "receiving"]
  /\ parent' = [parent EXCEPT ![n] = m]
  /\ UNCHANGED <<sum, acked>>

Echo(n, m) ==
  /\ phase[n] = "receiving"
  /\ <<n, m>> \in R
  /\ m # n
  /\ phase' = [phase EXCEPT ![n] = "echoing"]
  /\ UNCHANGED <<parent, sum, acked>>

Reply(n) ==
  /\ phase[n] = "echoing"
  /\ parent[n] # NoNode
  /\ n \notin acked[parent[n]]
  /\ sum' = [sum EXCEPT ![parent[n]] = sum[parent[n]] + n]
  /\ acked' = [acked EXCEPT ![parent[n]] = acked[parent[n]] \cup {n}]
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ UNCHANGED parent

RootReply ==
  /\ phase[initiator] = "echoing"
  /\ phase' = [phase EXCEPT ![initiator] = "done"]
  /\ UNCHANGED <<parent, sum, acked>>

TestSpec == Init /\ [][Send(_)]_vars
            /\ [][Recv(_, _)]_vars
            /\ [][Echo(_, _)]_vars
            /\ [][Reply(_)]_vars
            /\ [][RootReply]_vars

TypeOK ==
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ phase \in [Node -> {"idle", "sent", "receiving", "echoing", "done"}]
  /\ sum \in [Node -> SUBSET Node]
  /\ acked \in [Node -> SUBSET Node]

AncestorProperties ==
  /\ \A n \in Node \ {initiator} : parent[n] # NoNode
  /\ \A m, n \in Node : (m # NoNode /\ parent[n] = m) => parent[m] # n
====