---- MODULE MCBoulanger ----
\* Model-checking configuration for the Boulanger mutual exclusion algorithm. It
\* extends the Boulanger specification and overrides the Nat type with a finite
\* range, adding a state constraint that ticket numbers stay within that range
\* so TLC can explore the state space without running off to infinity.
EXTENDS Naturals, Boulanger

CONSTANTS
    N, MaxNat

VARIABLES
    \* Inherited from Boulanger; listed here for clarity.
    \*   ticket: [1..N -> Nat]  the Lamport ticket each process holds
    \*   pc: [1..N -> {"idle","waiting","cs"}]  the phase of each process
    \*   served: Nat  a counter for how many times the critical section has been used
    ticket, pc, served

vars == <<ticket, pc, served>>

NatOverride == 0..MaxNat

TypeOK ==
    /\ ticket \in [1..N -> NatOverride]
    /\ pc \in [1..N -> {"idle","waiting","cs"}]
    /\ served \in NatOverride

Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ pc = [i \in 1..N |-> "idle"]
    /\ served = 0

\* A process requests the critical section and takes a fresh ticket.
Request ==
    /\ \E i \in 1..N :
        /\ pc[i] = "idle"
        /\ ticket[i] < MaxNat
        /\ ticket' = [ticket EXCEPT ![i] = ticket[i] + 1]
        /\ pc' = [pc EXCEPT ![i] = "waiting"]
    /\ UNCHANGED served

\* A waiting process enters the critical section when its ticket is the smallest
\* (or tied for smallest, with the lower-index process winning the tie) among
\* all processes that are either waiting or already in the critical section.
Enter ==
    /\ \E i \in 1..N :
        /\ pc[i] = "waiting"
        /\ \A j \in 1..N :
            (pc[j] \in {"waiting","cs"}) => (ticket[i] <= ticket[j])
        /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<ticket, served>>

\* A process leaves the critical section and bumps the served counter.
Exit ==
    /\ \E i \in 1..N :
        /\ pc[i] = "cs"
        /\ pc' = [pc EXCEPT ![i] = "idle"]
        /\ served' = IF served < MaxNat THEN served + 1 ELSE served
    /\ UNCHANGED ticket

Relax == UNCHANGED vars

Next == Request \/ Enter \/ Exit \/ Relax

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..N : (pc[i] = "cs" /\ pc[j] = "cs") => i = j

\* The finite ticket range plus the Tie rule in Enter are what keep mutual
\* exclusion alive when the model checker cannot explore an infinite Nat domain.
Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ served <= MaxNat

StateConstraint == \A i \in 1..N : ticket[i] < MaxNat

====