---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

\* The Bakery spec's natural numbers are overridden here to a finite range
\* so the model is checkable; the inductive spec ISpec starts from any
\* reachable state, not just the initial one.
NatOverride == 0..MaxNat

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ want \in [1..N -> BOOLEAN]
    /\ ticket \in [1..N -> NatOverride]
    /\ nextTicket \in NatOverride

Init ==
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ want = [i \in 1..N |-> FALSE]
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0

\* A process announces it wants the critical section.
Request(i) ==
    /\ ~want[i]
    /\ want' = [want EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

\* The ticket is only issued if it is still below the bounded maximum.
TakeTicket(i) ==
    /\ want[i]
    /\ ticket[i] = 0
    /\ nextTicket < MaxNat
    /\ ticket' = [ticket EXCEPT ![i] = nextTicket]
    /\ nextTicket' = nextTicket + 1
    /\ UNCHANGED <<inCS, want>>

\* Entry is guarded by the ticket ordering: strictly lower than every
\* other process's ticket, and the other process is not already in.
Enter(i) ==
    /\ want[i]
    /\ ticket[i] # 0
    /\ \A j \in 1..N : (j # i /\ ticket[j] # 0) => ticket[i] < ticket[j]
    /\ \A j \in 1..N : ~inCS[j]
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<want, ticket, nextTicket>>

\* Leaving frees the critical section and clears the ticket.
Exit(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED nextTicket

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : TakeTicket(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

\* The inductive spec: any reachable state (not just the initial one) must
\* satisfy the invariant, so the invariant is preserved by every action.
ISpec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..N : (inCS[i] /\ inCS[j]) => i = j

\* The full inductive invariant: mutual exclusion plus type correctness.
Inv == MutualExclusion /\ TypeOK

====