---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES cs, ticket, inCS, served

vars == <<cs, ticket, inCS, served>>

Bump(x) == IF x < MaxNat THEN x + 1 ELSE x

TypeOK ==
  /\ cs \in 0..N
  /\ ticket \in [1..N -> 0..MaxNat]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ served \in 0..MaxNat

Init ==
  /\ cs = 0
  /\ ticket = [i \in 1..N |-> 0]
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ served = 0

Enter(i) ==
  /\ cs = 0
  /\ ~inCS[i]
  /\ cs' = i
  /\ ticket' = [ticket EXCEPT ![i] = Bump(@)]
  /\ UNCHANGED <<inCS, served>>

Serve(i) ==
  /\ cs = i
  /\ ~inCS[i]
  /\ inCS' = [inCS EXCEPT ![i] = TRUE]
  /\ served' = Bump(@)
  /\ UNCHANGED <<cs, ticket>>

Exit(i) ==
  /\ cs = i
  /\ inCS[i]
  /\ cs' = 0
  /\ ticket' = [ticket EXCEPT ![i] = Bump(@)]
  /\ inCS' = [inCS EXCEPT ![i] = FALSE]
  /\ UNCHANGED served

Next == \E i \in 1..N : Enter(i) \/ Serve(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion == \A i \in 1..N : inCS[i] => (cs = i)

Inv == TypeOK /\ MutualExclusion

ISpec == Spec

NatOverride(x) == IF x <= MaxNat THEN x ELSE MaxNat

====