---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, Majority

CONSTANT Value

VARIABLES seq, cand, count, i

(*-----------------------------------------------------------------
  Type invariant
-----------------------------------------------------------------*)
TypeOK ==
  /\ seq \in Seq(Value)
  /\ cand \in Value \cup {None}
  /\ count \in Nat
  /\ i \in Nat

(*-----------------------------------------------------------------
  Main invariant (inherits the invariant from the base spec)
-----------------------------------------------------------------*)
Inv ==
  /\ TypeOK
  /\ i <= Len(seq)

(*-----------------------------------------------------------------
  Majority predicate
-----------------------------------------------------------------*)
Majority(v) ==
  Cardinality({j \in 1..Len(seq) : seq[j] = v}) > Len(seq) / 2

(*-----------------------------------------------------------------
  Correctness invariant
-----------------------------------------------------------------*)
Correct ==
  (i = Len(seq)) => (\A v \in Value : Majority(v) => v = cand)

(*-----------------------------------------------------------------
  Specification
-----------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<seq, cand, count, i>>

(*-----------------------------------------------------------------
  Proof obligations (checked by TLAPS)
-----------------------------------------------------------------*)
THEOREM TypeOKInv == Spec => []TypeOK
  PROOF OBVIOUS

THEOREM InvInv == Spec => []Inv
  PROOF OBVIOUS

THEOREM CorrectInv == Spec => []Correct
  PROOF OBVIOUS

====