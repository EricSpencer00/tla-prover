---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* ------------------------------------------------------------------- *)
(* Value set of possible elements *)
ValueSet == {A, B, C}

(* ------------------------------------------------------------------- *)
(* BoundedSeq(V) yields all sequences over V whose length is at most bound *)
BoundedSeq(V) == { s \in Seq(V) : Len(s) <= bound }

(* ------------------------------------------------------------------- *)
(* Variables *)
VARIABLES seq, i, cand, cnt

vars == <<seq, i, cand, cnt>>

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cnt = 0
    /\ cand \in ValueSet

(* ------------------------------------------------------------------- *)
(* One step of the Boyer‑Moore scan *)
Next ==
    /\ i <= Len(seq)
    /\ LET cur == seq[i] IN
       IF cnt = 0 THEN
           /\ cand' = cur
           /\ cnt' = 1
       ELSE IF cur = cand THEN
           /\ cand' = cand
           /\ cnt' = cnt + 1
       ELSE
           /\ cand' = cand
           /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq
  \/ (* stuttering when the scan is finished *)
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, cand, cnt, i>>

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

(* ------------------------------------------------------------------- *)
(* Majority predicate for a value v *)
Majority(v) ==
    LET n == Len(seq) IN
    ( Cardinality({ j \in 1..n : seq[j] = v }) > n / 2 )

(* ------------------------------------------------------------------- *)
(* Correctness property: after a complete scan, any true majority element
   must be the candidate *)
Correct ==
    ( i > Len(seq) ) => ( \A v \in ValueSet : Majority(v) => cand = v )

(* ------------------------------------------------------------------- *)
(* Inductive invariant (a simple strengthening of TypeOK) *)
Inv == TypeOK

====