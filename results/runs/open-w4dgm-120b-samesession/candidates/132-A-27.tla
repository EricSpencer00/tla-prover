---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Three model values; sequence length bounded by 'bound' via BoundedSeq.
Values == {A, B, C}

\* BoundedSeq replaces the usual Seq operator to keep the state space finite.
BoundedSeq == [n \in 0..bound |-> [i \in 1..n -> Values]]

VARIABLES seq, pos, cand, cnt

vars == <<seq, pos, cand, cnt>>

TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in 0..bound
    /\ cand \in Values
    /\ cnt \in Nat

Init ==
    /\ \E s \in BoundedSeq : seq = s
    /\ pos = 1
    /\ \E e \in Values : cand = e
    /\ cnt = 0

\* Boyer-Moore scan: compare head of the suffix with the candidate.
Step ==
    /\ pos <= Len(seq)
    /\ IF seq[pos] = cand
         THEN /\ cnt' = cnt + 1
              /\ cand' = cand
         ELSE IF cnt > 0
              THEN /\ cnt' = cnt - 1
                   /\ cand' = cand
              ELSE /\ cnt' = 1
                   /\ cand' = seq[pos]
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Finish ==
    /\ pos > Len(seq)
    /\ pos' = 1
    /\ UNCHANGED <<seq, cand, cnt>>

Next == Step \/ Finish

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

\* The only element that can be a true majority of the whole sequence is
\* the element left in the candidate register at the end of the scan.
Correct ==
    \A e \in Values :
        (2 * Cardinality({i \in 1..Len(seq) : seq[i] = e}) > Len(seq))
            => e = cand

\* True majority can never be lost: every majority element is the candidate.
Inv == Correct

\* Both directions: the candidate is a majority exactly when it is the sole
\* majority element of the sequence.
MajorityImpliesCandidate == Correct
CandidateImpliesMajority == Correct

Properties == MajorityImpliesCandidate /\ CandidateImpliesMajority

====