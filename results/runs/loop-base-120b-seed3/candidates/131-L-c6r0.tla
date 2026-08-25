---- MODULE MajorityProof ----
EXTENDS Majority, FiniteSets, Sequences, Naturals

CONSTANT Value

(* ---------------------------------------------------------------------- *)
(*   Inherited state variables and definitions are taken from Majority.   *)
(* ---------------------------------------------------------------------- *)

Init == Majority!Init
Next == Majority!Next
vars == Majority!vars

(* ---------------------------------------------------------------------- *)
(*   Specification of the whole system                                    *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(*   Invariants (imported from the main specification)                    *)
(* ---------------------------------------------------------------------- *)

TypeOK == Majority!TypeOK
Correct == Majority!Correct
Inv    == Majority!Inv

(* ---------------------------------------------------------------------- *)
(*   Proof that TypeOK is an invariant                                      *)
(* ---------------------------------------------------------------------- *)

THEOREM TypeOKIsInvariant ==
  ASSUME Init, Next
  PROVE []TypeOK
PROOF
  <1>1. Init => TypeOK
        BY Majority!InitTypeOK
  <1>2. ∀ \<<\>> \in [][Next]_vars :
        (TypeOK /\ TypeOK')
        BY Majority!NextPreservesTypeOK
  <1>3. []TypeOK
        FROM <1>1, <1>2
        BY INVARIANT_DEF
  QED

(* ---------------------------------------------------------------------- *)
(*   Proof that Correct is an invariant                                     *)
(* ---------------------------------------------------------------------- *)

THEOREM CorrectIsInvariant ==
  ASSUME Init, Next
  PROVE []Correct
PROOF
  <1>1. Init => Correct
        BY Majority!InitCorrect
  <1>2. ∀ \<<\>> \in [][Next]_vars :
        (Correct /\ Correct')
        BY Majority!NextPreservesCorrect
  <1>3. []Correct
        FROM <1>1, <1>2
        BY INVARIANT_DEF
  QED

(* ---------------------------------------------------------------------- *)
(*   Proof that Inv is an invariant                                         *)
(* ---------------------------------------------------------------------- *)

THEOREM InvIsInvariant ==
  ASSUME Init, Next
  PROVE []Inv
PROOF
  <1>1. Init => Inv
        BY Majority!InitInv
  <1>2. ∀ \<<\>> \in [][Next]_vars :
        (Inv /\ Inv')
        BY Majority!NextPreservesInv
  <1>3. []Inv
        FROM <1>1, <1>2
        BY INVARIANT_DEF
  QED

====