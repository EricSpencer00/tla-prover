---- MODULE MajorityProof ----
EXTENDS Majority, Sequences, FiniteSets, TLC

CONSTANT Value

(* Type correctness invariant *)
TypeOK == /\ seq \in Seq(Value)
        /\ pos \in 1..|seq|+1
        /\ candidate \in Value \cup {NONE}
        /\ count \in Integers

(* Main correctness invariant: any strict majority element equals candidate *)
Correct == \A v \in Value :
              (Cardinality({ i \in 1..|seq| : seq[i] = v }) > |seq|/2) => candidate = v

(* Supporting inductive invariant used by the algorithm *)
Inv == (candidate = NONE => count = 0)
      /\ (candidate \neq NONE =>
           /\ count > 0
           /\ count = Cardinality({ i \in 1..pos-1 : seq[i] = candidate }) -
                       Cardinality({ i \in 1..pos-1 : seq[i] \neq candidate }))

Spec == Majority.Spec

INVARIANTS TypeOK Correct Inv

THEOREM Spec_Invariant_Inv:
  Spec => []Inv
PROOF
  ...
QED

THEOREM Spec_Invariant_Correct:
  Spec => []Correct
PROOF
  ...
QED

THEOREM Spec_Invariant_TypeOK:
  Spec => []TypeOK
PROOF
  ...
QED

====