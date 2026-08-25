---- MODULE MCMajority ----
EXTENDS Sequences, FiniteSets, Naturals

CONSTANTS A, B, C, bound

\* Set of possible element values
ValueSet == { A, B, C }

\* Finite version of Seq: all functions from 1..n to S for some n ≤ bound
BoundedSeq(S) == UNION { [1..n -> S] : n \in 0..bound }

\* State variables
VARIABLES seq, i, cand, cnt

\* Length of the current sequence
SeqLen == Len(seq)

\* Initial state
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* Scan the next element using the Boyer‑Moore three‑case logic
Scan ==
    /\ i <= SeqLen
    /\ LET x == seq[i] IN
         IF cnt = 0 THEN
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

\* Next-state relation
Next ==
    \/ Scan
    \/ /\ i > SeqLen
       /\ UNCHANGED <<seq, i, cand, cnt>>

\* Complete specification
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ i \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* Helper: number of occurrences of v in the current sequence
Count(v) == Cardinality({ j \in 1..SeqLen : seq[j] = v })

\* Safety property: any true majority element must equal the final candidate
Correct ==
    /\ i > SeqLen
    /\ \A v \in ValueSet :
         (Count(v) > SeqLen / 2) => v = cand

\* Inductive invariant (simple but sufficient for the model)
Inv ==
    /\ cnt >= 0
    /\ (cnt = 0 => cand \in ValueSet)

====