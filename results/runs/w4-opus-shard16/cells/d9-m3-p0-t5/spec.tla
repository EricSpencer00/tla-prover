-------------------------- MODULE W4Od9m3p0t5 --------------------------
EXTENDS Naturals

CONSTANTS Nodes, Admin, NoOne, MaxTerm

Actors == Nodes \cup {Admin}

VARIABLES
    term,       \* current election term
    leader,     \* current leader node, or NoOne
    using       \* using[a] = TRUE iff actor a is actuating the breaker

vars == << term, leader, using >>

TypeOK ==
    /\ term \in 0..MaxTerm
    /\ leader \in (Nodes \cup {NoOne})
    /\ using \in [Actors -> BOOLEAN]

Init ==
    /\ term = 0
    /\ leader = NoOne
    /\ using = [a \in Actors |-> FALSE]

\* Failover election: with no leader, a node wins the next term.
Elect(n) ==
    /\ leader = NoOne
    /\ term < MaxTerm
    /\ leader' = n
    /\ term' = term + 1
    /\ UNCHANGED using

\* The leader begins actuating only when the breaker is idle.
Enter(n) ==
    /\ leader = n
    /\ \A a \in Actors : ~using[a]
    /\ using' = [using EXCEPT ![n] = TRUE]
    /\ UNCHANGED << term, leader >>

\* The leader stops actuating.
Leave(n) ==
    /\ leader = n
    /\ using[n]
    /\ using' = [using EXCEPT ![n] = FALSE]
    /\ UNCHANGED << term, leader >>

\* The leader fails: actuation cleared, leadership vacated for failover.
Fail(n) ==
    /\ leader = n
    /\ leader' = NoOne
    /\ using' = [using EXCEPT ![n] = FALSE]
    /\ UNCHANGED term

\* Admin override: forcibly stop every node, revoke leadership, take control.
AdminSeize ==
    /\ ~using[Admin]
    /\ using' = [a \in Actors |-> a = Admin]
    /\ leader' = NoOne
    /\ UNCHANGED term

\* Admin hands the breaker back.
AdminRelease ==
    /\ using[Admin]
    /\ using' = [using EXCEPT ![Admin] = FALSE]
    /\ UNCHANGED << term, leader >>

Next ==
    \/ \E n \in Nodes : Elect(n)
    \/ \E n \in Nodes : Enter(n)
    \/ \E n \in Nodes : Leave(n)
    \/ \E n \in Nodes : Fail(n)
    \/ AdminSeize
    \/ AdminRelease

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: never two distinct actors actuating at once.
MutualExclusion ==
    \A a, b \in Actors : (using[a] /\ using[b]) => (a = b)

=============================================================================
