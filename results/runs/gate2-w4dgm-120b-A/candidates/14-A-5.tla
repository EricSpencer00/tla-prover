---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES token, inCS, wants, servedCount, ticket

vars == <<token, inCS, wants, servedCount, ticket>>

Init ==
    /\ token = 0
    /\ inCS = [p \in 1..N |-> FALSE]
    /\ wants = [p \in 1..N |-> FALSE]
    /\ servedCount = [p \in 1..N |-> 0]
    /\ ticket = [p \in 1..N |-> 0]

Request(p) ==
    /\ ~wants[p]
    /\ token # p
    /\ wants' = [wants EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<token, inCS, servedCount, ticket>>

Enter(p) ==
    /\ token = p
    /\ wants[p]
    /\ ~inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = TRUE]
    /\ servedCount' = [servedCount EXCEPT ![p] = (servedCount[p] + 1) % (MaxNat + 1)]
    /\ UNCHANGED <<token, wants, ticket>>

Exit(p) ==
    /\ inCS[p]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ wants' = [wants EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<token, servedCount, ticket>>

PassToken(p) ==
    /\ token = p
    /\ ~inCS[p]
    /\ token' = (p % N) + 1
    /\ UNCHANGED <<inCS, wants, servedCount, ticket>>

AdminRevoke(p) ==
    /\ ticket[p] < MaxNat
    /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
    /\ inCS' = [inCS EXCEPT ![p] = FALSE]
    /\ wants' = [wants EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<token, servedCount>>

Next ==
    \/ \E p \in 1..N : Request(p) \/ Enter(p) \/ Exit(p) \/ PassToken(p) \/ AdminRevoke(p)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A p \in 1..N : inCS[p] => (token = p)

TypeOK ==
    /\ token \in 1..N
    /\ inCS \in [1..N -> BOOLEAN]
    /\ wants \in [1..N -> BOOLEAN]
    /\ servedCount \in [1..N -> 0..MaxNat]
    /\ ticket \in [1..N -> 0..MaxNat]

Inv ==
    \A p \in 1..N : inCS[p] => (token = p)

NatOverride == Nat

====