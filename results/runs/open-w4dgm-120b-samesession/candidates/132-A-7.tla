---- MODULE MCMajority ----
EXTENDS Integers, Sequences

CONSTANTS A, B, C, bound

Values == {A, B, C}

\* BoundedSeq is a finitary version of Seq used to keep the model finite.
\* It is defined here and replaces the standard Seq operator from Sequences.
BoundedSeq(S) == IF S = {} THEN << >> ELSE CHOOSE f \in S : \A g \in S : Len(g) <= Len(f)

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

TypeOK ==
    /\ seq \in BoundedSeq([1..bound -> Values])
    /\ pos \in 1..(bound + 1)
    /\ cand \in Values
    /\ counter \in 0..bound

Init ==
    /\ seq \in BoundedSeq([1..bound -> Values])
    /\ pos = 1
    /\ cand \in Values
    /\ counter = 0

\* Boyer-Moore scan: three cases depending on the counter and the next element.
Next ==
    \/ \E v \in Values :
        /\ pos <= bound
        /\ seq' = [seq EXCEPT ![pos] = v]
        /\ pos' = pos + 1
        /\ IF pos = 1 THEN cand' = v ELSE cand' = cand
        /\ IF pos = 1 THEN counter' = 1
           ELSE IF cand = v THEN counter' = counter + 1
           ELSE IF counter > 0 THEN counter' = counter - 1
           ELSE cand' = v /\ counter' = 1
    \/ UNCHANGED <<seq, pos, cand, counter>>

Spec == Init /\ [][Next]_vars
    /\ WF_vars(Next)

\* Any true majority element must equal the candidate after a complete scan.
Correct ==
    /\ pos = bound + 1
    /\ \A v \in Values : (2 * Cardinality({i \in 1..bound : seq[i] = v}) > bound) => v = cand

\* The Boyer-Moore candidate stays non-empty whenever the scanned prefix
\* already holds a strict majority, so the counter never drops out from under it.
Inv ==
    /\ \A i \in 1..(pos - 1) : (2 * Cardinality({j \in 1..(pos - 1) : seq[j] = cand}) > (pos - 1)) => counter > 0
    /\ pos >= 1

\* Weak fairness: the scan always eventually reaches the end of the sequence.
Complete == (pos # bound + 1) ~> (pos = bound + 1)

====