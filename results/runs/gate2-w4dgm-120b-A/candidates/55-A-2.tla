---- MODULE MCEcho ----
EXTENDS Naturals

CONSTANTS Node, initiator, R, NoNode

ASSUME NoNode \notin Node

VARIABLES pending, acks, parent, replies, sent

vars == <<pending, acks, parent, replies, sent>>

Init ==
    /\ pending = [n \in Node |-> [active |-> FALSE, done |-> FALSE]]
    /\ acks = [n \in Node |-> {}]
    /\ parent = [n \in Node |-> NoNode]
    /\ replies = [n \in Node |-> 0]
    /\ sent = [n \in Node |-> 0]
    /\ pending' = [pending EXCEPT ![initiator] = [active |-> TRUE, done |-> FALSE]]
    /\ UNCHANGED <<acks, parent, replies, sent>>

Send(n) ==
    /\ pending[n].active
    /\ ~pending[n].done
    /\ sent[n] < R
    /\ sent' = [sent EXCEPT ![n] = sent[n] + 1]
    /\ UNCHANGED <<pending, acks, parent, replies>>

Deliver(n, m) ==
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = m]
    /\ pending' = [pending EXCEPT ![n] = [active |-> FALSE, done |-> FALSE]]
    /\ UNCHANGED <<acks, replies, sent>>

Reply(n) ==
    /\ parent[n] # NoNode
    /\ replies' = [replies EXCEPT ![parent[n]] = replies[parent[n]] + 1]
    /\ UNCHANGED <<pending, acks, parent, sent>>

Ack(n, m) ==
    /\ parent[n] = m
    /\ replies[n] > 0
    /\ pending[n].active
    /\ replies' = [replies EXCEPT ![n] = replies[n] - 1]
    /\ acks' = [acks EXCEPT ![m] = acks[m] \cup {n}]
    /\ UNCHANGED <<pending, parent, sent>>

Done(n) ==
    /\ parent[n] = NoNode
    /\ pending[n].active
    /\ replies[n] = 0
    /\ replies' = [replies EXCEPT ![n] = 1]
    /\ UNCHANGED <<pending, acks, parent, sent>>

Settle(n) ==
    \/ Reply(n)
    \/ Done(n)

Next ==
    \/ \E n \in Node : Send(n)
    \/ \E n \in Node, m \in Node : Deliver(n, m)
    \/ \E n \in Node : Reply(n)
    \/ \E n \in Node, m \in Node : Ack(n, m)
    \/ \E n \in Node : Done(n)

Spec == Init /\ [][Next]_vars /\ \A n \in Node : SF_vars(Settle(n))

TypeOK ==
    /\ pending \in [Node -> [active : BOOLEAN, done : BOOLEAN]]
    /\ acks \in [Node -> SUBSET Node]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ replies \in [Node -> 0..R]
    /\ sent \in [Node -> 0..R]

AncestorProperties ==
    /\ (\A n \in Node : parent[n] = NoNode => n = initiator)
    /\ (\A n \in Node : parent[n] # NoNode => parent[n] \in acks[parent[n]])
    /\ (\A n \in Node : parent[n] # NoNode => initiator \in acks[n])

TestSpec == Spec /\ TypeOK /\ AncestorProperties

N1 == {"a", "b", "c"}
I1 == {"a"}
R1 == 2

====