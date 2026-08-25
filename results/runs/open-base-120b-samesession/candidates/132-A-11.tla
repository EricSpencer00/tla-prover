---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

(* the set of possible element values *)
ElemSet == {A, B, C}

(* a finite version of Seq: all functions from 1..k to S for k ≤ n *)
BoundedSeq(S, n) == UNION { [i \in 1..k -> S] : k \in 0..n }

(* the concrete set of sequences used in the model *)
Seqs == BoundedSeq(ElemSet, bound)

VARIABLES seq, i, cand, cnt

(* initial state *)
Init ==
    /\ seq \in Seqs
    /\ i = 1
    /\ cnt = 0
    /\ cand \in ElemSet

(* one step of the Boyer‑Moore scan *)
Step ==
    /\ i <= Len(seq)
    /\ LET x == seq[i] IN
        IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
        ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
        ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

(* allow stuttering after the scan is finished *)
Next ==
    \/ Step
    \/ /\ i > Len(seq)
       /\ UNCHANGED <<seq, i, cand, cnt>>

(* the full specification *)
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

(* type correctness invariant *)
TypeOK ==
    /\ seq \in Seqs
    /\ i \in Nat
    /\ cnt \in Nat
    /\ cand \in ElemSet

(* definition of a majority element in the current sequence *)
Majority(m) == Cardinality({j \in 1..Len(seq) : seq[j] = m}) > Len(seq) / 2

(* safety property: if a true majority exists, the final candidate equals it *)
Correct ==
    \A m \in ElemSet :
        ( Majority(m) => ( i > Len(seq) => cand = m ) )

(* processed positions so far *)
Processed == 1..(i - 1)

(* inductive invariant of the algorithm *)
Inv ==
    /\ (cnt = 0)
       \/ (cand \in ElemSet
           /\ cnt = Cardinality({j \in Processed : seq[j] = cand})
                  - Cardinality({j \in Processed : seq[j] # cand}))
           
====