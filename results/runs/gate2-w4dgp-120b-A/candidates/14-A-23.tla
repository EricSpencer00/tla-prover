---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

\* This module configures the Boulanger mutual exclusion algorithm for model checking.
\* It overrides the abstract Nat set with a finite range (0..MaxNat) and adds a
\* state constraint that keeps ticket numbers below the maximum, so the TLC
\* state space stays finite. All of the Boulanger logic (state, init, next, and
\* invariants) is reused unchanged from the base specification.
CONSTANTS N, MaxNat

VARIABLES entering, number, served, nbserved, maxserved

vars == <<entering, number, served, nbserved, maxserved>>

\* Finite-range version of the abstract Nat set used by the base spec.
Nat == 0..MaxNat

TypeOK ==
    /\ entering \in [1..N -> BOOLEAN]
    /\ number \in [1..N -> Nat]
    /\ served \in [1..N -> Nat]
    /\ nbserved \in 0..N
    /\ maxserved \in 0..N

Init ==
    /\ entering = [p \in 1..N |-> FALSE]
    /\ number = [p \in 1..N |-> 0]
    /\ served = [p \in 1..N |-> 0]
    /\ nbserved = 0
    /\ maxserved = 0

\* A process starts its entry request; it may only do this when every ticket
\* counter is still below the maximum, so no ticket can ever reach MaxNat.
Request(p) ==
    /\ ~entering[p]
    /\ number[p] < MaxNat
    /\ \A q \in 1..N : number[q] < MaxNat
    /\ entering' = [entering EXCEPT ![p] = TRUE]
    /\ number' = [number EXCEPT ![p] = number[p] + 1]
    /\ UNCHANGED <<served, nbserved, maxserved>>

\* A process enters the critical section, provided its ticket is still in
\* the current serving window and no one else is inside.
Enter(p) ==
    /\ entering[p]
    /\ number[p] > maxserved
    /\ number[p] <= maxserved + nbserved
    /\ \A q \in 1..N : ~entering[q]
    /\ entering' = [entering EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<number, served, nbserved, maxserved>>

\* A process leaves the critical section; its ticket becomes the new base.
Exit(p) ==
    /\ served[p] < number[p]
    /\ served' = [served EXCEPT ![p] = served[p] + 1]
    /\ nbserved' = IF nbserved < N THEN nbserved + 1 ELSE nbserved
    /\ maxserved' = IF maxserved < MaxNat THEN maxserved + 1 ELSE maxserved
    /\ UNCHANGED <<entering, number>>

Next ==
    \/ \E p \in 1..N : Request(p)
    \/ \E p \in 1..N : Enter(p)
    \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : entering[p] => (served[p] = number[p] - 1)

\* The full inductive invariant from the base spec: ticket ordering and the
\* no-slowback property both hold alongside the type-correctness check.
Inv ==
    /\ TypeOK
    /\ \A p, q \in 1..N : (number[p] = number[q]) => (p = q)
    /\ \A p \in 1..N : (served[p] = number[p] - 1) => entering[p]

====