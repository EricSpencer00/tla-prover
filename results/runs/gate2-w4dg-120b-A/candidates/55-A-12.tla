---- MODULE MCEcho ----
EXTENDS Naturals, FiniteSets

\* Fully-meshed three-node graph.  NoNode is the sentinel for "no parent".
CONSTANTS Node, initiator, R, NoNode

VARIABLES senders, epoch, parent, clock

vars == <<senders, epoch, parent, clock>>

TypeOK ==
    /\ senders \in [Node -> BOOLEAN]
    /\ epoch \in Nat
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ clock \in Nat

\* An initiator with no parent starts the echo wave.
Init ==
    /\ senders = [n \in Node |-> n = initiator]
    /\ epoch = 0
    /\ parent = [n \in Node |-> IF n = initiator THEN NoNode ELSE NoNode]
    /\ clock = 0

\* Send an echo to a neighbour; R is the mesh, so the send is always possible.
SendEcho(n, m) ==
    /\ senders[n]
    /\ n # m
    /\ parent' = [parent EXCEPT ![m] = n]
    /\ senders' = [senders EXCEPT ![n] = FALSE, ![m] = TRUE]
    /\ epoch' = epoch + 1
    /\ UNCHANGED <<clock>>

Advance(n) ==
    /\ ~senders[n]
    /\ clock' = (clock + 1) % 3
    /\ UNCHANGED <<senders, epoch, parent>>

Next == \E n \in Node : Advance(n) \/ (\E m \in Node : SendEcho(n, m))

AncestorChain(x) == IF parent[x] = NoNode THEN <<>> ELSE <<parent[x]>> \o Triangle(AncestorChain(parent[x]))

\* The initiator ends up as ancestor of every other node; the mesh digraph is acyclic.
AncestorProperties ==
    /\ \A x \in Node \ {initiator} : initiator \in SetOfSeq(AncestorChain(x))
    /\ \A x \in Node : initiator \notin SetOfSeq(AncestorChain(parent[x]))

TestSpec == Init /\ [][Next]_vars

====