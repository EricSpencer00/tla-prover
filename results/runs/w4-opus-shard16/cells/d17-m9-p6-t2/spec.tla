-------------------------- MODULE W4Od17m9p6t2 --------------------------
EXTENDS Naturals

CONSTANTS Nodes, Chutes, MaxEpoch

VARIABLES
    curEpoch,       \* hub's current epoch
    known,          \* known[n] : epoch each node last learned
    active,         \* active[c] : is chute c currently assigned for routing?
    activeEpoch     \* activeEpoch[c] : the epoch under which c was activated

vars == << curEpoch, known, active, activeEpoch >>

TypeOK ==
    /\ curEpoch \in 0..MaxEpoch
    /\ known \in [Nodes -> 0..MaxEpoch]
    /\ active \in [Chutes -> BOOLEAN]
    /\ activeEpoch \in [Chutes -> 0..MaxEpoch]

Init ==
    /\ curEpoch = 0
    /\ known = [n \in Nodes |-> 0]
    /\ active = [c \in Chutes |-> FALSE]
    /\ activeEpoch = [c \in Chutes |-> 0]

\* Reconfigure: retire the old epoch and clear all chutes.
Reconfigure ==
    /\ curEpoch < MaxEpoch
    /\ curEpoch' = curEpoch + 1
    /\ active' = [c \in Chutes |-> FALSE]
    /\ UNCHANGED << known, activeEpoch >>

\* A node catches up to the current epoch.
Adopt(n) ==
    /\ known[n] < curEpoch
    /\ known' = [known EXCEPT ![n] = curEpoch]
    /\ UNCHANGED << curEpoch, active, activeEpoch >>

\* A current node activates a chute, stamping it with the epoch it knows.
Activate(n, c) ==
    /\ known[n] = curEpoch
    /\ ~active[c]
    /\ active' = [active EXCEPT ![c] = TRUE]
    /\ activeEpoch' = [activeEpoch EXCEPT ![c] = known[n]]
    /\ UNCHANGED << curEpoch, known >>

\* A current node deactivates a chute.
Deactivate(n, c) ==
    /\ known[n] = curEpoch
    /\ active[c]
    /\ active' = [active EXCEPT ![c] = FALSE]
    /\ UNCHANGED << curEpoch, known, activeEpoch >>

Next ==
    \/ Reconfigure
    \/ \E n \in Nodes : Adopt(n)
    \/ \E n \in Nodes, c \in Chutes : Activate(n, c)
    \/ \E n \in Nodes, c \in Chutes : Deactivate(n, c)

Spec == Init /\ [][Next]_vars

\* No stale action in effect: every active chute was stamped current.
NoStaleActive ==
    \A c \in Chutes : active[c] => (activeEpoch[c] = curEpoch)

=============================================================================
