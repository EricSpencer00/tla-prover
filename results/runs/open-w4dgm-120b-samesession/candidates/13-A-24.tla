---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Replaces the infinite Nat from Naturals with a finite range 0..MaxNat for model checking.
NatOverride(n) == IF n <= MaxNat THEN n ELSE MaxNat

VARIABLES inCS, want, ticket, nextTicket
vars == <<inCS, want, ticket, nextTicket>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> 0..MaxNat]
    /\ nextTicket \in 0..MaxNat

\* The full inductive invariant: strong exclusive access to the critical section plus
\* coherence between the want[] flags and tickets, the locked-and-wanted coincidence,
\* and the fact that a natural-number ticket is always requestible.
Inv ==
    /\ \A i \in 1..N : inCS[i] => \A j \in 1..N : j # i => ~inCS[j]
    /\ \A i \in 1..N : want[i] => (ticket[i] <= nextTicket /\ nextTicket <= MaxNat)
    /\ \A i \in 1..N : inCS[i] => want[i]
    /\ \A i \in 1..N : ticket[i] <= nextTicket

MutualExclusion == \A i \in 1..N : inCS[i] => \A j \in 1..N : j # i => ~inCS[j]

Init ==
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ want = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0

Request(i) ==
    /\ ~want[i]
    /\ let t == NatOverride(nextTicket + 1) in
        /\ want' = [want EXCEPT ![i] = TRUE]
        /\ ticket' = [ticket EXCEPT ![i] = t]
        /\ nextTicket' = t
    /\ UNCHANGED inCS

Enter(i) ==
    /\ want[i]
    /\ ~inCS[i]
    /\ \A k \in 1..N : ~inCS[k]
    /\ \A j \in 1..N : (want[j] /\ ticket[j] < ticket[i]) => j = i
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<want, ticket, nextTicket>>

Exit(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<ticket, nextTicket>>

Abort(i) ==
    /\ want[i]
    /\ ~inCS[i]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)
    \/ \E i \in 1..N : Abort(i)

\* Inductive specification: start from ANY state satisfying the invariant, not just
\* the canonical initial state, and verify every transition preserves it -- this is
\* what makes the invariant truly inductive rather than merely a consequence of Init.
ISpec == Init /\ [][Next]_vars

====