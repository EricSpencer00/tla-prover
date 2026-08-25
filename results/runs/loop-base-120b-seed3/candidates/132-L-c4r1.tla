---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* The set of possible element values *)
ValueSet == {A, B, C}

(* Finite sequences whose length does not exceed the bound *)
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

VARIABLES seq, i, cand, cnt

(* Count the number of occurrences of v in sequence s *)
Count(s, v) ==
    Cardinality({ j \in 1..Len(s) : s[j] = v })

(* Initial state *)
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt = 0

(* One step of the Boyer‑Moore scan *)
Next ==
    \/ /\ i <= Len(seq)
       /\ LET x == seq[i] IN
            \/ /\ cnt = 0
               /\ cand' = x
               /\ cnt'  = 1
            \/ /\ cnt > 0 /\ cand = x
               /\ cand' = cand
               /\ cnt'  = cnt + 1
            \/ /\ cnt > 0 /\ cand # x
               /\ cand' = cand
               /\ cnt'  = cnt - 1
       /\ i' = i + 1
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* Full specification with weak fairness on Next *)
Spec ==
    Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_{<<seq, i, cand, cnt>>}(Next)

(* Type correctness invariant *)
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i   \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

(* Correctness: any true majority element must equal the final candidate *)
Correct ==
    /\ i > Len(seq) =>
        \A v \in ValueSet :
            (2 * Count(seq, v) > Len(seq)) => cand = v

(* Inductive invariant – we reuse TypeOK as a simple invariant *)
Inv == TypeOK
====