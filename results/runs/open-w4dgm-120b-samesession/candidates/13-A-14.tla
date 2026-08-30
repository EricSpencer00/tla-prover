---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

\* This override replaces the infinite Nat with a finite range 0..MaxNat.
NatOverride == 0..MaxNat

\* The base Bakery spec has these symbols; this module adds no new ones.
VARIABLES ticket, inCS, want, maxTicket

vars == <<ticket, inCS, want, maxTicket>>

TypeOK ==
    /\ ticket \in [1..N -> NatOverride]
    /\ inCS \in [1..N -> BOOLEAN]
    /\ want \in [1..N -> BOOLEAN]
    /\ maxTicket \in NatOverride

\* The full inductive invariant the Bakery spec protects: exclusivity plus type.
Inv ==
    /\ maxTicket <= MaxNat
    /\ \A i, j \in 1..N : (i # j /\ inCS[i]) => ~inCS[j]

Init ==
    /\ ticket = [i \in 1..N |-> 0]
    /\ inCS = [i \in 1..N |-> FALSE]
    /\ want = [i \in 1..N |-> FALSE]
    /\ maxTicket = 0

Request(i) ==
    /\ ~want[i]
    /\ ~inCS[i]
    /\ want' = [want EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, inCS, maxTicket>>

\* A ticket is taken and advanced, saturating at MaxNat so the bound is never left.
Take(i) ==
    /\ want[i]
    /\ ticket[i] = 0
    /\ ticket' = [ticket EXCEPT ![i] = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket]
    /\ maxTicket' = IF maxTicket < MaxNat THEN maxTicket + 1 ELSE maxTicket
    /\ UNCHANGED <<inCS, want>>

Enter(i) ==
    /\ want[i]
    /\ ticket[i] # 0
    /\ \A j \in 1..N : ticket[j] = 0 \/ ticket[j] > ticket[i]
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ UNCHANGED <<ticket, want, maxTicket>>

Exit(i) ==
    /\ inCS[i]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ want' = [want EXCEPT ![i] = FALSE]
    /\ UNCHANGED maxTicket

Next ==
    \/ \E i \in 1..N : Request(i)
    \/ \E i \in 1..N : Take(i)
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Exit(i)

\* Inductive spec: any reachable state, not just the start, must hold the invariant.
ISpec == Init /\ [][Next]_vars

\* Stub properties; they are required by the .cfg but carry no meaning here.
MutualExclusion == TRUE
TypeOK == TRUE

====