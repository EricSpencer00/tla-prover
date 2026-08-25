---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

ASSUME bound \in Nat

(* The set of possible element values *)
Values == { A, B, C }

(* Finite sequences over Values whose length does not exceed the bound *)
BoundedSeq == { s \in Seq(Values) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

vars == << seq, i, cand, cnt >>

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

(* One step of the Boyer‑Moore scan *)
Next ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
         IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt'  = 1
         ELSE IF x = cand THEN
            /\ cand' = cand
            /\ cnt'  = cnt + 1
         ELSE
            /\ cand' = cand
            /\ cnt'  = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

(* Full specification *)
Spec == Init /\ [][Next]_vars

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat
    /\ i <= Len(seq) + 1

(* Helper to count occurrences of an element in a sequence *)
Count(seq, e) ==
    Cardinality({ j \in 1..Len(seq) : seq[j] = e })

(* Correctness property: any strict majority must equal the final candidate *)
Correct ==
    /\ i = Len(seq) + 1
    /\ \A e \in Values :
         (Count(seq, e) > Len(seq) / 2) => cand = e

(* Simple inductive invariant useful for model checking *)
Inv ==
    /\ cnt \in Nat
    /\ cnt <= Len(seq)

====