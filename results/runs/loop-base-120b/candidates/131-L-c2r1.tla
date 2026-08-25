---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets
CONSTANT Value

(* Import the main majority‑vote specification. *)
INSTANCE Majority WITH Value <- Value

(* Re‑export the main specification and its components. *)
Spec == Majority!Spec
Init == Majority!Init
Next == Majority!Next

(* Invariants defined in the main specification. *)
TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv    == Majority!Inv

(* ----------------------------------------------------------------------
   Proof that TypeOK is an invariant of Spec.
   ---------------------------------------------------------------------- *)
THEOREM TypeOKInv == Spec => []TypeOK
PROOF
  <1>1. Init => TypeOK
      BY Majority!InitTypeOK
  <1>2. \A s \in [State -> BOOLEAN] : (TypeOK /\ Next) => TypeOK'
      BY Majority!NextPreservesTypeOK
  <1>3. QED
      BY <1>1, <1>2, TemporalInduction

(* ----------------------------------------------------------------------
   Proof that Correct is an invariant of Spec.
   ---------------------------------------------------------------------- *)
THEOREM CorrectInv == Spec => []Correct
PROOF
  <1>1. Init => Correct
      BY Majority!InitCorrect
  <1>2. \A s \in [State -> BOOLEAN] : (Correct /\ Next) => Correct'
      BY Majority!NextPreservesCorrect
  <1>3. QED
      BY <1>1, <1>2, TemporalInduction

(* ----------------------------------------------------------------------
   Proof that Inv is an invariant of Spec.
   ---------------------------------------------------------------------- *)
THEOREM InvInv == Spec => []Inv
PROOF
  <1>1. Init => Inv
      BY Majority!InitInv
  <1>2. \A s \in [State -> BOOLEAN] : (Inv /\ Next) => Inv'
      BY Majority!NextPreservesInv
  <1>3. QED
      BY <1>1, <1>2, TemporalInduction
====