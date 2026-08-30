---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, want, serving, servedCount, ticket

vars == <<inCS, want, serving, servedCount, ticket>>

\* The type override: Nat is replaced by the finite range 0..MaxNat here.
NatOverride == 0..MaxNat

TypeOK ==
    /\ inCS \in 0..N
    /\ want \in 0..N
    /\ serving \in 0..N
    /\ servedCount \in 0..N
    /\ ticket \in [1..N -> NatOverride]

Init ==
    /\ inCS = 0
    /\ want = 0
    /\ serving = 0
    /\ servedCount = 0
    /\ ticket = [p \in 1..N |-> 0]

\* The full set of bakery actions (request, enter, exit, reissue) is inherited
\* from the Bakery specification -- they are unchanged here.

Next ==
    \/ \E p \in 1..N :
         /\ want' = IF want < N THEN want + 1 ELSE N
         /\ ticket' = [ticket EXCEPT ![p] = IF ticket[p] = 0 THEN 1 ELSE ticket[p] + 1]
         /\ UNCHANGED <<inCS, serving, servedCount>>
    \/ \E p \in 1..N :
         /\ ticket[p] # 0
         /\ inCS = 0
         /\ \A q \in 1..N : ticket[q] = 0 \/ ticket[p] <= ticket[q]
         /\ inCS' = inCS + 1
         /\ serving' = 1
         /\ want' = want - 1
         /\ ticket' = [ticket EXCEPT ![p] = 0]
         /\ UNCHANGED servedCount
    \/ \E p \in 1..N :
         /\ ticket[p] # 0
         /\ ticket' = [ticket EXCEPT ![p] = ticket[p] + 1]
         /\ UNCHANGED <<inCS, want, serving, servedCount>>
    \/ \E p \in 1..N :
         /\ ticket[p] # 0
         /\ (inCS > 0 \/ (\E q \in 1..N : ticket[q] # 0 /\ ticket[p] > ticket[q]))
         /\ ticket' = [ticket EXCEPT ![p] = ticket[p] - 1]
         /\ UNCHANGED <<inCS, want, serving, servedCount>>
    \/ \E p \in 1..N :
         /\ ticket[p] # 0
         /\ inCS = 0
         /\ \A q \in 1..N : ticket[q] = 0 \/ ticket[p] <= ticket[q]
         /\ inCS' = inCS + 1
         /\ serving' = 1
         /\ want' = want - 1
         /\ ticket' = [ticket EXCEPT ![p] = ticket[p] - 1]
         /\ UNCHANGED servedCount
    \/ inCS > 0
         /\ inCS' = inCS - 1
         /\ serving' = 0
         /\ servedCount' = IF servedCount < N THEN servedCount + 1 ELSE N
         /\ UNCHANGED <<want, ticket>>

MutualExclusion == inCS <= 1

Inv ==
    / inCS >= 0
    /\ inCS = serving
    /\ want + inCS + serving + servedCount = N

ISpec == Init /\ [][Next]_vars

====