---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

Operators == [parent : Node \cup {NoNode}, state : {"idle", "active", "done"}, anc : SUBSET Node]

\* The Echo algorithm on a fully-meshed three-node graph; the graph is implicit and
\* complete, so any two distinct nodes are neighbors.
\* LIVENESS is omitted in this model-checking configuration: the initiator's echo
\* may be arbitrarily slow to start, and termination is not guaranteed to be reachable.
\* The test purpose is the ancestor-safety property, which the fully-meshed graph
\* helps satisfy without relying on progress.

VARIABLES op

TypeOK == \A n \in Node : op[n] \in Operators

Init == [n \in Node |-> [parent |-> NoNode, state |-> "idle", anc |-> {}]]

StartEcho(n)   == op[initiator].state = "idle"
                   /\ op' = [op EXCEPT ![initiator] = [parent |-> NoNode, state |-> "active", anc |-> {}]]

Visit(n, p)    == op[n].state = "idle"
                   /\ p # n
                   /\ op[p].state = "active"
                   /\ op' = [op EXCEPT ![n] = [parent |-> p, state |-> "active", anc |-> @.anc \cup {p}]]

Terminate(n)   == op[n].state = "active"
                   /\ (n = initiator \/ op[n].parent # NoNode)
                   /\ op' = [op EXCEPT ![n] = [parent |-> @.parent, state |-> "done", anc |-> @.anc]]


Next == \E n \in Node : StartEcho(n) \/ Terminate(n) \/ (\E p \in Node : Visit(n p)

\* A test variant that prints the graph adjacency relation; not part of the model.
PrintAdj == \E n \in Node : \E p \in Node :
                /\ n # p
                /\ op' = [op EXCEPT ![n] = [parent |-> op[n].parent, state |-> op[n].state, anc |-> op[n].anc]]
                /\ UNCHANGED op

Spec == Init /\ [][Next]_op

AncestorProperties ==
    /\ (\A m \in Node : m # initiator => initiator \in op[m].anc)
    /\ (\A x \in Node : x # initiator => (op[x].parent # NoNode => op[x].parent \in op[x].anc))
    /\ (\A a \in Node : a \in op[initiator].anc => a = initiator)

TestSpec == Spec /\ (PrintAdj /\ TRUE)

====