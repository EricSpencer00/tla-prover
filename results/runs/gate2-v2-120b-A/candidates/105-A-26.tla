---- MODULE DyadicRationals ----
EXTENDS Integers, Sequences, TLC

(*-----------------------------------------------------------------
  Record definition for a dyadic rational: a numerator and a denominator.
  Both fields are integers, and the denominator is always positive.
-----------------------------------------------------------------*)
RECORD_TYPE == [num : Int, den : PosInt]

(*-----------------------------------------------------------------
  The set of all dyadic rationals, represented as records.
-----------------------------------------------------------------*)
DyadicSet == { r \in RECURSIVE RecordConstructor : r.den > 0 }

(*-----------------------------------------------------------------
  Constant values
-----------------------------------------------------------------*)
One == [num |-> 1, den |-> 1]
Half == [num |-> 0, den |-> 2] \* not used directly, but kept for completeness

(*-----------------------------------------------------------------
  Normalization operator: repeatedly halve numerator and denominator
  while both are even.
-----------------------------------------------------------------*)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(*-----------------------------------------------------------------
  State variable
-----------------------------------------------------------------*)
VARIABLE p

(*-----------------------------------------------------------------
  Initial state: any dyadic rational (including the special constant One)
-----------------------------------------------------------------*)
Init ==
  /\ p \in DyadicSet
  /\ p = One

(*-----------------------------------------------------------------
  Next-state relation:
  - Either stay in the current state (stuttering)
  - Or replace p by its normalized form (which may be the same)
-----------------------------------------------------------------*)
Next ==
  \/ UNCHANGED p
  \/ /\ p' = Norm(p)

(*-----------------------------------------------------------------
  The specification of the system
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<p>>

(*-----------------------------------------------------------------
  Optional auxiliary definitions (not required by the .cfg but useful)
-----------------------------------------------------------------*)
Inv == p \in DyadicSet

TypeOK == /\ p \in DyadicSet

=============================================================================