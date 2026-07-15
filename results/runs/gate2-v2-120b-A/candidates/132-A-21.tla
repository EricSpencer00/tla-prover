---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, TLC

(***************************************************************************)
(* Constants from the configuration                                         *)
(*   A, B, C : the three distinct values                                    *)
(*   bound   : maximal sequence length (natural number)                     *)
(*   Seq     : the set of all finite sequences over {A,B,C} of length ≤bound*)
(***************************************************************************)

CONSTANTS A, B, C, bound, Seq

(* ---------------------------------------------------------------------- *)
(* Derived constant representing the domain of elements                     *)
(* ---------------------------------------------------------------------- *)
ElemSet == {A, B, C}

(* ---------------------------------------------------------------------- *)
(* Variables representing the state of the majority vote algorithm         *)
(* ---------------------------------------------------------------------- *)
VARIABLES seq, i, cand, cnt

(* ---------------------------------------------------------------------- *)
(* Helper definitions                                                    *)
(* ---------------------------------------------------------------------- *)

(* Length of the current sequence (0 if seq = <<>>) *)
SeqLen == IF seq = <<>> THEN 0 ELSE Len(seq)

(* Index of the first element (if any) *)
FirstIdx == 1

(* ---------------------------------------------------------------------- *)
(* Initial predicate                                                     *)
(* ---------------------------------------------------------------------- *)
Init ==
  /\ seq \in Seq
  /\ i = FirstIdx
  /\ cand \in ElemSet
  /\ cnt = 0

(* ---------------------------------------------------------------------- *)
(* Step action: process the element at position i, then advance i          *)
(* ---------------------------------------------------------------------- *)
Next ==
  /\ i <= SeqLen
  /\ LET x == seq[i] IN
       /\ IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt'  = 1
          ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt'  = cnt + 1
          ELSE
            /\ cand' = cand
            /\ cnt'  = cnt - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

(* ---------------------------------------------------------------------- *)
(* Stuttering step when the scan is complete                               *)
(* ---------------------------------------------------------------------- *)
Stutter ==
  /\ i > SeqLen
  /\ UNCHANGED <<seq, i, cand, cnt>>

(* ---------------------------------------------------------------------- *)
(* Overall step relation                                                  *)
(* ---------------------------------------------------------------------- *)
Step ==
  \/ Next
  \/ Stutter

(* ---------------------------------------------------------------------- *)
(* Specification                                                         *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Step]_<<seq, i, cand, cnt>>

(* ---------------------------------------------------------------------- *)
(* Safety (type correctness) invariant                                    *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  /\ seq \in Seq
  /\ i \in Nat
  /\ (i = 0) \/ (i >= 1 /\ i <= SeqLen + 1)
  /\ cand \in ElemSet
  /\ cnt \in Nat

(* ---------------------------------------------------------------------- *)
(* Correctness property: after a full scan, any majority element equals the*)
(* current candidate.                                                     *)
(* ---------------------------------------------------------------------- *)
Correct ==
  /\ i > SeqLen
  /\ \A v \in ElemSet :
        (Cardinality({j \in 1..SeqLen : seq[j] = v}) > SeqLen / 2) => cand = v

(* ---------------------------------------------------------------------- *)
(* Inductive invariant (useful for model checking)                        *)
(* ---------------------------------------------------------------------- *)
Inv ==
  /\ TypeOK
  /\ (i > SeqLen => Correct)

(* ---------------------------------------------------------------------- *)
(* The set of all sequences over ElemSet of length up to bound             *)
(* ---------------------------------------------------------------------- *)
SeqDef ==
  { s \in Seq(ElemSet) : Len(s) <= bound }

(* ---------------------------------------------------------------------- *)
(* Constrain the Seq constant to the bounded set defined above             *)
(* ---------------------------------------------------------------------- *)
SeqConstr == Seq = SeqDef

(* ---------------------------------------------------------------------- *)
(* Theorem: the invariant Inv is indeed an invariant of Spec               *)
(* ---------------------------------------------------------------------- *)
THEOREM InvIsInvariant == Spec => []Inv

====