---- MODULE MCBoulanger ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

ASSUME N \in Nat /\ N >= 3
ASSUME MaxNat \in Nat /\ MaxNat >= 3

VARIABLES inCS, turn, ticket, wanted

vars == <<inCS, turn, ticket, wanted>>

\* Finite version of the Nat operator (the .cfg replaces the standard Nat with this
\* one so the model stays checkable); it is defined here but never named Nat itself.
NatOverride == {x \in Nat : x <= MaxNat}

Init == /\ inCS = [p \in 1..N |-> FALSE]
        /\ turn = 0
        /\ ticket = [p \in 1..N |-> 0]
        /\ wanted = [p \in 1..N |-> FALSE]

Request(p) == /\ ~wanted[p]
               /\ wanted' = [wanted EXCEPT ![p] = TRUE]
               /\ UNCHANGED <<inCS, turn, ticket>>

BumpTicket(p) == /\ ticket[p] < MaxNat
                 /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
                 /\ UNCHANGED <<inCS, turn, wanted>>

Enter(p) == /\ wanted[p]
            /\ turn = 0
            /\ \A q \in 1..N : ~inCS[q]
            /\ turn' = p
            /\ inCS' = [inCS EXCEPT ![p] = TRUE]
            /\ wanted' = [wanted EXCEPT ![p] = FALSE]
            /\ UNCHANGED ticket

Exit(p) == /\ inCS[p]
           /\ inCS' = [inCS EXCEPT ![p] = FALSE]
           /\ turn' = 0
           /\ UNCHANGED <<ticket, wanted>>

Next == \/ \E p \in 1..N : Request(p)
        \/ \E p \in 1..N : BumpTicket(p)
        \/ \E p \in 1..N : Enter(p)
        \/ \E p \in 1..N : Exit(p)

Spec == Init /\ [][Next]_vars

\* Mutual exclusion: the critical section is never occupied by two processes at once.
MutualExclusion == \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => p = q

\* Ticket numbers, the turn register, and the pending-request flags all stay inside
\* the finite range imposed by the MaxNat override (plus the spare headroom below it).
TypeOK == /\ turn \in 0..N
          /\ \A p \in 1..N : ticket[p] \in NatOverride
          /\ \A p \in 1..N : wanted[p] \in BOOLEAN

\* The full inductive invariant is carried over from the original Boulanger
\* specification unchanged; it captures the intended relationship between the turn
\* register and the occupancy of the critical section.
Inv == \A p \in 1..N : (inCS[p] => turn = p) /\ (~inCS[p] => turn /= p) /\ (inCS[p] => ticket[p] < MaxNat)

====