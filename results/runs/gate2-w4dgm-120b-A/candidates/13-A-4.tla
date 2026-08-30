---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* Finite override: Nat becomes a bounded range so ticket numbers stay
\* within the model-checking window.
NatOverride == 0..MaxNat

VARIABLES inCS, reg, turn, ticket, want

Vars == <<inCS, reg, turn, ticket, want>>

TypeOK ==
    /\ inCS \in [1..N -> BOOLEAN]
    /\ reg \in NatOverride
    /\ turn \in 0..N
    /\ ticket \in [1..N -> NatOverride]
    /\ want \in [1..N -> BOOLEAN]

\* The full invariant: mutual exclusion plus type correctness.
Inv ==
    /\ MutualExclusion
    /\ TypeOK
    /\ \A i \in 1..N : inCS[i] => (turn = i /\ ticket[i] <= reg)

Init ==
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ reg = 0
    /\ turn = 0
    /\ ticket = [i \in 1..N |-> 0]
    /\ want = [i \in 1..N |-> FALSE]

Request(i) ==
    /\ ~want[i]
    /\ ~inCS[i]
    /\ turn # i
    /\ want' = [want EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<inCS, reg, turn, ticket>>

\* Ticket numbers do not exceed MaxNat; a bounded window keeps the model finite.
Acquire(i) ==
    /\ \A j \in 1..N : ~inCS[j]
    /\ want[i]
    /\ turn' = i
    /\ ticket' = [ticket EXCEPT ![i] = reg + 1]
    /\ UNCHANGED <<inCS, reg, want>>

Enter(i) ==
    /\ turn = i
    /\ ~inCS[i]
    /\ reg = ticket[i]
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<reg, turn, ticket, want>>

\* Leaving advances the register, releasing the ticket window.
Leave(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ reg' = IF reg < MaxNat THEN reg + 1 ELSE reg
    /\ turn' = 0
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ want' = [want EXCEPT ![i] = FALSE]

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Acquire(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Leave(i)

ISpec == Init /\ [][Next]_Vars

====