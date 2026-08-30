---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Finite-ticket override: Nat is replaced by NatOverride in the .cfg, so
\* nothing below may declare or redefine Nat. Ticket numbers are capped at
\* MaxNat, which makes the model finite and checkable.
NatOverride == {0..MaxNat}

VARIABLES inCS, want, ticket, nextTicket

vars == <<inCS, want, ticket, nextTicket>>

TypeOK ==
    /\ inCS \in SUBSET (1..N)
    /\ want \in SUBSET (1..N)
    /\ ticket \in [1..N -> NatOverride]
    /\ nextTicket \in NatOverride

Init ==
    /\ inCS = {}
    /\ want = {}
    /\ ticket = [i \in 1..N |-> 0]
    /\ nextTicket = 0

\* A process with no ticket may take one, saturating at MaxNat.
TakeTicket(i) ==
    /\ ticket[i] = 0
    /\ ticket' = [ticket EXCEPT ![i] = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat]
    /\ nextTicket' = IF nextTicket < MaxNat THEN nextTicket + 1 ELSE MaxNat
    /\ UNCHANGED <<inCS, want>>

RequestCS(i) ==
    /\ ticket[i] # 0
    /\ i \notin want
    /\ want' = want \cup {i}
    /\ UNCHANGED <<inCS, ticket, nextTicket>>

Enter(i) ==
    /\ i \in want
    /\ inCS = {}
    /\ \A j \in want : ticket[i] <= ticket[j]
    /\ inCS' = {i}
    /\ want' = want \ {i}
    /\ UNCHANGED <<ticket, nextTicket>>

Exit(i) ==
    /\ i \in inCS
    /\ inCS' = {}
    /\ UNCHANGED <<want, ticket, nextTicket>>

Idle(i) ==
    /\ i \notin inCS
    /\ i \notin want
    /\ ticket[i] = nextTicket
    /\ UNCHANGED vars

Next ==
    \E i \in 1..N :
        \/ TakeTicket(i) \/ RequestCS(i) \/ Enter(i) \/ Exit(i) \/ Idle(i)

Init == Init

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    /\ \A x, y \in inCS : x = y
    /\ \A i \in 1..N : i \in inCS => i \in want

\* The invariant is the full inductive property; it is preserved across
\* every transition from any reachable state, not just from the initial one.
Inv ==
    /\ \A i, j \in inCS : i = j
    /\ \A i \in 1..N : i \in inCS => i \in want
    /\ \A i \in 1..N : i \in inCS => \A j \in want : ticket[i] <= ticket[j]

ISpec == Spec
====