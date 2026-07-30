---- MODULE MCEcho ----
EXTENDS Integers, FiniteSets

CONSTANTS Node, initiator, R, NoNode

N1 == Node
I1 == initiator
R1 == R

VARIABLES parent, done, acked

vars == <<parent, done, acked>>

RECURSIVE Ancestors(_)
Ancestors(n) ==
    IF parent[n] = NoNode
        THEN {}
        ELSE {parent[n]} \cup Ancestors(parent[n])

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ done = [n \in Node |-> "idle"]
    /\ acked = [n \in Node |-> "none"]

SendEcho(n) ==
    /\ done[n] = "idle"
    /\ n = initiator
    /\ done' = [done EXCEPT ![n] = "sent"]
    /\ UNCHANGED <<parent, acked>>

ReceiveEcho(n, p) ==
    /\ done[p] = "sent"
    /\ parent[n] = NoNode
    /\ parent' = [parent EXCEPT ![n] = p]
    /\ done' = [done EXCEPT ![n] = "sent"]
    /\ UNCHANGED acked

Reply(n) ==
    /\ done[n] = "sent"
    /\ n # initiator
    /\ acked' = [acked EXCEPT ![n] = "replied"]
    /\ done' = [done EXCEPT ![n] = "done"]
    /\ UNCHANGED parent

Done(n) ==
    /\ done[n] = "sent"
    /\ ParentDone(n)
    /\ acked' = [acked EXCEPT ![n] = "replied"]
    /\ done' = [done EXCEPT ![n] = "done"]
    /\ UNCHANGED parent

ParentDone(n) ==
    IF parent[n] = initiator THEN TRUE
    ELSE done[parent[n]] = "done"

Next ==
    \/ \E n \in Node : SendEcho(n)
    \/ \E n \in Node, p \in Node : ReceiveEcho(n, p)
    \/ \E n \in Node : Reply(n)
    \/ \E n \in Node : Done(n)

Spec == Init /\ [][Next]_vars

TestSpec ==
    /\ Spec
    /\ Println("MCEcho runs over a fully-meshed graph of nodes:")
    /\ Println(Node)

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ done \in [Node -> {"idle", "sent", "done"}]
    /\ acked \in [Node -> {"none", "replied"}]

AncestorProperties ==
    /\ \A n \in Node : initiator \in Ancestors(n)
    /\ \A x, y \in Node : (x \in Ancestors(y) /\ y \in Ancestors(x)) => x = y

====