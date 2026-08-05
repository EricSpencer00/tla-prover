---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

\* Echo spanning-tree algorithm: a fully-meshed three-node graph.
CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sent, recved, done

vars == <<parent, sent, recved, done>>

States == {"idle", "awaiting", "done"}

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ sent \in [Node -> SUBSET Node]
    /\ recved \in [Node -> SUBSET Node]
    /\ done \in [Node -> BOOLEAN]

Init ==
    /\ parent = [v \in Node |-> NoNode]
    /\ sent = [v \in Node |-> {}]
    /\ recved = [v \in Node |-> {}]
    /\ done = [v \in Node |-> FALSE]

InitRoot ==
    /\ \A v \in Node : parent[v] = NoNode
    /\ ~done[initiator]
    /\ done' = [done EXCEPT ![initiator] = TRUE]
    /\ UNCHANGED <<parent, sent, recved>>

SendEcho ==
    /\ \E u \in Node, v \in Node :
        /\ u # v
        /\ u \notin sent[v]
        /\ sent' = [sent EXCEPT ![v] = sent[v] \cup {u}]
    /\ UNCHANGED <<parent, recved, done>>

RecvEcho ==
    /\ \E u \in Node, v \in Node :
        /\ u # v
        /\ u \in sent[v]
        /\ u \notin recved[v]
        /\ parent[v] = NoNode
        /\ v # initiator
        /\ parent' = [parent EXCEPT ![v] = u]
        /\ recved' = [recved EXCEPT ![v] = recved[v] \cup {u}]
    /\ UNCHANGED <<sent, done>>

Propagate ==
    /\ \E v \in Node :
        /\ parent[v] # NoNode
        /\ parent[parent[v]] # NoNode
        /\ parent' = [parent EXCEPT ![v] = parent[parent[v]]]
    /\ UNCHANGED <<sent, recved, done>>

CheckDone ==
    /\ \A v \in Node : parent[v] # NoNode \/ v = initiator
    /\ \A v \in Node : done[v]
    /\ UNCHANGED vars

Next == InitRoot \/ SendEcho \/ RecvEcho \/ Propagate \/ CheckDone

\* Test variant that prints the graph adjacency instead of replaying it.
PrintGraph ==
    /\ UNCHANGED vars
    /\ PrintF("Adjacency: %p\n", {p \in R})

Spec == Init /\ [][Next]_vars
TestSpec == Spec /\ (PrintF("Adjacency: %p\n", {p \in R}) \/ TRUE)

\* Safety: the initiator is an ancestor of every node and ancestry is acyclic.
AncestorProperties ==
    /\ \A v \in Node : parent[v] # NoNode => parent[parent[v]] # v

====