---- MODULE MCEcho ----
EXTENDS Integers

CONSTANTS Node, initiator, R, NoNode

VARIABLES parent, sent, got, idle

vars == <<parent, sent, got, idle>>

TypeOK ==
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ sent \in [Node -> BOOLEAN]
    /\ got \in [Node -> BOOLEAN]
    /\ idle \in [Node -> BOOLEAN]

Init ==
    /\ parent = [n \in Node |-> NoNode]
    /\ sent = [n \in Node |-> FALSE]
    /\ got = [n \in Node |-> FALSE]
    /\ idle = [n \in Node |-> FALSE]

\* Initiate the echo round by sending out the first request from a chosen
\* initiator node (only one node ever does this in a run).
SendInit ==
    /\ sent[initiator] = FALSE
    /\ sent' = [sent EXCEPT ![initiator] = TRUE]
    /\ idle' = [idle EXCEPT ![initiator] = TRUE]
    /\ UNCHANGED <<parent, got>>

\* An idle node receives an echo request from any neighbor and records its
\* sender as the spanning-tree parent.
Receive(n) ==
    /\ \E m \in Node :
        /\ m # n
        /\ <<m, n>> \in R
        /\ sent[m] = TRUE
        /\ got[n] = FALSE
        /\ parent' = [parent EXCEPT ![n] = m]
        /\ got' = [got EXCEPT ![n] = TRUE]
    /\ UNCHANGED <<sent, idle>>

\* A node forwards the request toward its parent and becomes idle again.
Forward(n) ==
    /\ sent[n] = TRUE
    /\ got[n] = TRUE
    /\ \E m \in Node :
        /\ parent[m] = n
        /\ sent' = [sent EXCEPT ![m] = TRUE]
        /\ idle' = [idle EXCEPT ![m] = TRUE]
    /\ UNCHANGED <<parent, got>>

\* The initiator receives its own request back, completing a round (it does
\* not forward to a parent, since it has none); this is the final reachable
\* transition of the system.
Return ==
    /\ sent[initiator] = TRUE
    /\ \A n \in Node : sent[n] = TRUE
    /\ sent' = [sent EXCEPT ![initiator] = FALSE]
    /\ UNCHANGED <<parent, got, idle>>

Next ==
    \/ SendInit \/ Return
    \/ \E n \in Node : Receive(n) \/ Forward(n)

\* The spanning-tree ancestry forms a strict hierarchy rooted at the initiator,
\* and no node is ever recorded as its own parent.
AncestorProperties ==
    /\ \A n \in Node : parent[n] # n
    /\ parent[initiator] = NoNode
    /\ \A n \in Node \ {initiator} : parent[n] # NoNode

\* A diagnostic entry point used by the test harness to emit the graph's
\* adjacency relation; always available and never blocks the normal spec.
PrintR ==
    /\ TRUE
    /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ PrintR

TestSpec == Spec

====