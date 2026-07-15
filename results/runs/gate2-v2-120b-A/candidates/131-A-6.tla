---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* Constants *)
CONSTANT Value

(***************************************************************************)
(* Helper definitions *)
Pos == 1 .. Len(seq)              \* positions in the input sequence
Seq == seq                        \* alias for readability

\* A finite set of values used for type correctness
ValueSet == {v \in Value : TRUE}

(***************************************************************************)
(* Variables *)
VARIABLES cand, cnt, i, seq

(***************************************************************************)
(* Initialization *)
Init ==
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt \in Nat
    /\ seq \in Seq

(***************************************************************************)
(* Transition relation *)
Next ==
    \/ /\ i <= Len(seq)
       /\ cand' = seq[i]
       /\ cnt' = 1
       /\ i' = i + 1
    \/ /\ i <= Len(seq)
       /\ cand' = cand
       /\ cnt' = cnt + 1
       /\ i' = i + 1
    \/ /\ i <= Len(seq)
       /\ cand' = cand
       /\ cnt' = cnt - 1
       /\ i' = i + 1
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<cand, cnt, i, seq>>

(***************************************************************************)
(* Specification and actions *)
Spec == Init /\ [][Next]_<<cand, cnt, i, seq>>

(***************************************************************************)
(* Invariant: type correctness *)
TypeOK ==
    /\ i \in Nat
    /\ cnt \in Nat
    /\ cand \in ValueSet
    /\ seq \in Seq

(***************************************************************************)
(* Inductive invariant from the main specification (for safety proof) *)
Inv ==
    /\ i \in Pos \/ i = Len(seq) + 1
    /\ (i = 1) => cnt = 0
    /\ (i > 1) =>
         IF cnt = 0 THEN
             cand \in ValueSet /\ cnt = 0
         ELSE
             cand \in ValueSet /\ cnt > 0

(***************************************************************************)
(* Safety property: algorithm correctness after processing the entire seq *)
Correct ==
    /\ i = Len(seq) + 1
    /\ \A v \in ValueSet :
          ( Cardinality({j \in Pos : seq[j] = v}) >
            Cardinality(Pos) / 2 )
          => v = cand

(***************************************************************************)
(* Specification formula as required by the cfg *)
SpecFormula == Spec

=============================================================================