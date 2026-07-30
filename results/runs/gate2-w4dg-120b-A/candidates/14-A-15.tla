---- MODULE MCBoulanger ----
EXTENDS Naturals

CONSTANTS N, MaxNat, Nat

VARIABLES cs
vars == <<cs>>

None == "none"
Players == 1..N

Init0 == [p \in Players |-> None]

InCS == {p \in Players : cs[p] # None}

Spec ==
  /\ Init0
  /\ [][TRUE]_vars
  /\ TypeOK
  /\ Inv
  /\ MutualExclusion

TypeOK ==
  /\ cs \in [Players -> Players \cup {None}]

Inv ==
  /\ Cardinality(InCS) <= 1
  /\ cs[1] = None

MutualExclusion ==
  \A p, q \in Players : (cs[p] # None /\ cs[p] = cs[q]) => p = q

StateConstraint ==
  /\ \A p \in Players : cs[p] = None

====