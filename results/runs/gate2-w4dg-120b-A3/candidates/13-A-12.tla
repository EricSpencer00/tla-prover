---- MODULE MCBakery ----
EXTENDS Naturals

CONSTANTS N, MaxNat

VARIABLES num, inCS
vars == <<num, inCS>>

TypeOK ==
  /\ num \in 0 .. MaxNat
  /\ inCS \in BOOLEAN

Init ==
  /\ num = 0
  /\ inCS = FALSE

Enter ==
  /\ ~inCS
  /\ num' = (num + 1) % (MaxNat + 1)
  /\ inCS' = TRUE

Exit ==
  /\ inCS
  /\ inCS' = FALSE
  /\ UNCHANGED num

Next == Enter \/ Exit

Spec == Init /\ [][Next]_vars

ISpec == Spec /\ WF_vars(Enter) /\ WF_vars(Exit)

Inv ==
  /\ TypeOK
  /\ MutualExclusion
  /\ num \in 0 .. MaxNat

MutualExclusion ==
  MutualExclusionBase == (inCS => (inCS => TRUE))
  MutualExclusionBase

NatOverride ==
  Nat
====