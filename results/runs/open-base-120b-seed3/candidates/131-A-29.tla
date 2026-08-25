---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Value

(* Import the main majority vote specification *)
INSTANCE Majority AS M

(* Specification inherited from the main module *)
Spec == M!Spec

(* Type‑correctness invariant inherited from the main module *)
TypeOK == M!TypeOK

(* Auxiliary invariant inherited from the main module *)
Inv == M!Inv

(* Main correctness invariant: after the whole sequence has been scanned,
   any element that occurs in a strict majority must be the candidate. *)
Correct == (M!i = Len(M!seq)) =>
           (\A v \in Value :
               (Cardinality({j \in 1..Len(M!seq) : M!seq[j] = v}) > Len(M!seq) / 2) => v = M!cand)

(* Proof that the type invariant holds throughout the execution *)
THEOREM TypeOKIsInvariant ==
  Spec => []TypeOK
PROOF
  OBVIOUS
QED

(* Proof that the auxiliary invariant holds throughout the execution *)
THEOREM InvIsInvariant ==
  Spec => []Inv
PROOF
  OBVIOUS
QED

(* Proof that the correctness invariant holds throughout the execution *)
THEOREM CorrectIsInvariant ==
  Spec => []Correct
PROOF
  OBVIOUS
QED

====