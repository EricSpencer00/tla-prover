---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
Values == { A, B, C }

\* BoundedSeq replaces Seq from Sequences: a finite set of functions
BoundedSeq(n) == [1..n -> Values]

VARIABLES seq, i, cand, cnt, len

\* Type correctness invariant
TypeOK ==
    /\ len \in 0..bound
    /\ seq \in BoundedSeq(len)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* Count occurrences of a value in the current sequence
Count(v) == Cardinality({ j \in 1..len : seq[j] = v })

\* Correctness property: any true majority element must equal cand after scan
Correct ==
    (i > len) => 
        \A v \in Values : (Count(v) > len / 2) => v = cand

\* Inductive invariant (example)
Inv ==
    /\ cnt >= 0
    /\ i \in 1..len+1
    /\ (cnt = 0 => cand \in Values)

\* Initial state
Init ==
    /\ len \in 0..bound
    /\ seq \in BoundedSeq(len)
    /\ i = 1
    /\ cnt = 0
    /\ cand \in Values

\* Main transition: scanning the next element
Next ==
    /\ i <= len
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
        /\ seq' = seq
        /\ len' = len

\* Stuttering step after the scan is complete
NextStutter ==
    /\ i > len
    /\ UNCHANGED <<seq, i, cand, cnt, len>>

NextAction ==
    Next \/ NextStutter

\* Specification
Spec ==
    Init /\ [][NextAction]_<<seq, i, cand, cnt, len>>

====