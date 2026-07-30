---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Functions, Sequences

CONSTANTS A, B, C, bound

\* BoundedSeq replaces the unbounded Seq from Sequences with a version
\* whose domain is always a bounded initial segment of the naturals.
BoundedSeq(V) == { f \in FUNCTION [1..n, {V}] : n \in 0..bound }

VARIABLES seq, pos, cand, counter

vars == <<seq, pos, cand, counter>>

SeqSpace == BoundedSeq(A) \cup BoundedSeq(B) \cup BoundedSeq(C)

TypeOK ==
    /\ seq \in SeqSpace
    /\ pos \in 1..(bound + 1)
    /\ cand \in {A, B, C}
    /\ counter \in 0..bound

Init ==
    /\ seq \in SeqSpace
    /\ pos = 1
    /\ cand \in {A, B, C}
    /\ counter = 0

Next ==
    /\ pos <= bound
    /\ IF counter = 0
       THEN /\ cand' = seq[pos]
            /\ counter' = 1
       ELSE IF seq[pos] = cand
            THEN /\ counter' = counter + 1
                 /\ UNCHANGED cand
            ELSE /\ counter' = counter - 1
                 /\ UNCHANGED cand
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

\* A true majority element must equal the candidate after a complete scan.
Correct ==
    \A v \in {A, B, C} : (2 * Cardinality({i \in DOMAIN seq : seq[i] = v}) > Cardinality(seq)) => cand = v

\* The inductive-invariant version of Correct, without universal quantification.
Inv ==
    \A v \in {A, B, C} : (2 * Cardinality({i \in DOMAIN seq : seq[i] = v}) > Cardinality(seq)) => cand = v

Complete == pos > bound

SpecStrong == Spec /\ WF_vars(Next)

====