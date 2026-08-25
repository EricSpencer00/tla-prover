---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

(* --- Value set --------------------------------------------------- *)
ValueSet == { A, B, C }

(* --- Bounded sequences ------------------------------------------- *)
(*  Sequences over ValueSet whose length does not exceed the bound. *)
BoundedSeq == { s \in Seq(ValueSet) : Len(s) <= bound }

(* --- Variables --------------------------------------------------- *)
VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

(* --- Initialization ---------------------------------------------- *)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt = 0

(* --- Next-state relation ------------------------------------------ *)
Next ==
    \/ /\ i <= Len(seq)                     \* still elements to scan
       /\ LET cur == seq[i] IN
          IF cnt = 0 THEN
               /\ cand' = cur
               /\ cnt'  = 1
          ELSE IF cur = cand THEN
               /\ cand' = cand
               /\ cnt'  = cnt + 1
          ELSE
               /\ cand' = cand
               /\ cnt'  = cnt - 1
       /\ i' = i + 1
    \/ /\ i > Len(seq)                      \* scan finished
       /\ UNCHANGED << seq, i, cand, cnt >>

(* --- Specification ------------------------------------------------ *)
Spec == Init /\ [][Next]_vars

(* --- Type correctness invariant ----------------------------------- *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

(* --- Helper: count occurrences of a value in a sequence ------------ *)
Count(s, v) == Cardinality({ j \in DOMAIN s : s[j] = v })

(* --- Main correctness property ------------------------------------ *)
Correct ==
    /\ i > Len(seq)                         \* scan complete
    /\ \A v \in ValueSet :
         (Count(seq, v) * 2 > Len(seq)) => cand = v

(* --- Inductive invariant ------------------------------------------ *)
Inv ==
    /\ cnt \in Nat
    /\ cand \in ValueSet

====