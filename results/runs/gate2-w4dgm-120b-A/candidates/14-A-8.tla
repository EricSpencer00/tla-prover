---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Overrides the unbounded Nat from Naturals with a finite, checkable version.
NatOverride == {0, 1, 2, 3}

\* Bounded range for all natural-number variables in this model-checked spec.
Vars == {inCS, ticket, requesting}
\* inCS marks which process holds the critical section; ticket[n] is n's
\* request ticket; requesting[n] is whether n is still waiting for the section.

TypeOK ==
    /\ inCS \in 0 .. N
    /\ ticket \in [1 .. N -> 0 .. MaxNat]
    /\ requesting \in [1 .. N -> BOOLEAN]

Init ==
    /\ inCS = 0
    /\ ticket = [n \in 1 .. N |-> 0]
    /\ requesting = [n \in 1 .. N |-> FALSE]

\* A process marks its intent and takes a fresh ticket from the bounded pool.
Request(n) ==
    /\ requesting' = [requesting EXCEPT ![n] = TRUE]
    /\ ticket' = [ticket EXCEPT ![n] = IF @ < MaxNat THEN @ + 1 ELSE @]
    /\ UNCHANGED inCS

\* A non-slow process enters only when the section is free and its ticket
\* leads the waiting queue -- the mutual exclusion guard on inCS.
Enter(n) ==
    /\ requesting[n]
    /\ inCS = 0
    /\ \A m \in 1 .. N : (requesting[m] => ticket[n] <= ticket[m])
    /\ inCS' = n
    /\ UNCHANGED <<ticket, requesting>>

\* The current holder leaves the section.
Exit(n) ==
    /\ inCS = n
    /\ inCS' = 0
    /\ requesting' = [requesting EXCEPT ![n] = FALSE]
    /\ UNCHANGED ticket

Next ==
    \/ \E n \in 1 .. N : Request(n)
    \/ \E n \in 1 .. N : Enter(n)
    \/ \E n \in 1 .. N : Exit(n)

Spec == Init /\ [][Next]_Vars

\* SAFETY: mutual exclusion (at most one holder) and all variables within bounds.
MutualExclusion ==
    /\ (inCS # 0 => ~requesting[inCS])
    /\ \A n \in 1 .. N : requesting[n] => (inCS = 0 \/ ticket[n] <= ticket[inCS])
    /\ \A n \in 1 .. N : ticket[n] \in NatOverride
====