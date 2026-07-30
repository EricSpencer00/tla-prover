---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, MaxNat

VARIABLES inCS, number, waiting
vars == <<inCS, number, waiting>>

Init ==
  /\ inCS = [p \in 1..N |-> FALSE]
  /\ number = [p \in 1..N |-> 0]
  /\ waiting = [p \in 1..N |-> FALSE]

Request(p) ==
  /\ ~waiting[p]
  /\ waiting' = [waiting EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<inCS, number>>

Take(p) ==
  /\ waiting[p]
  /\ \A q \in 1..N : ~inCS[q]
  /\ number' = [number EXCEPT ![p] = (number[p] + 1) % (MaxNat + 1)]
  /\ inCS' = [inCS EXCEPT ![p] = TRUE]
  /\ waiting' = [waiting EXCEPT ![p] = FALSE]

Exit(p) ==
  /\ inCS[p]
  /\ inCS' = [inCS EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<number, waiting>>

Next ==
  \E p \in 1..N :
    \/ Request(p) \/ Take(p) \/ Exit(p)

InitState == Init

NextState == Next

TypeOK ==
  /\ inCS \in [1..N -> BOOLEAN]
  /\ number \in [1..N -> 0..MaxNat]
  /\ waiting \in [1..N -> BOOLEAN]

MutualExclusion ==
  \A p, q \in 1..N : (inCS[p] /\ inCS[q]) => (p = q)

Inv ==
  /\ TypeOK
  /\ MutualExclusion

ISpec == Init /\ [][Next]_vars

NatOverride == Nat

====