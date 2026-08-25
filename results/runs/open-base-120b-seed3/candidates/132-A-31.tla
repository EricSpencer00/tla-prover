---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* Set of possible element values
ElemSet == { A, B, C }

\* Bounded sequences of elements from ElemSet, length up to *bound*
BoundedSeq == { s \in [1..n -> ElemSet] : n \in 0..bound }

VARIABLES seq, pos, cand, cnt

\* Initial state
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in ElemSet
    /\ cnt = 0

\* Next-state relation (Boyer‑Moore scan)
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET x == seq[pos] IN
          /\ IF cnt = 0
                THEN /\ cand' = x
                     /\ cnt' = 1
                ELSE IF cand = x
                     THEN /\ cand' = cand
                          /\ cnt' = cnt + 1
                     ELSE /\ cand' = cand
                          /\ cnt' = cnt - 1
          /\ pos' = pos + 1
          /\ UNCHANGED seq
    \/ /\ pos > Len(seq)
       /\ UNCHANGED <<seq, pos, cand, cnt>>

\* Overall specification
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in ElemSet
    /\ cnt \in Nat

\* Counting occurrences of an element *e* in the current sequence
Count(e_) ==
    Cardinality({ i \in 1..Len(seq) : seq[i] = e_ })

\* Predicate that *e* is a majority element
HasMajority(e_) ==
    Count(e_) > Len(seq) / 2

MajorityExists == \E e \in ElemSet : HasMajority(e)

MajorityElem == CHOOSE e \in ElemSet : HasMajority(e)

\* Correctness: after the scan, any true majority must be the candidate
Correct ==
    (pos > Len(seq)) => (MajorityExists => cand = MajorityElem)

\* Inductive invariant (here we reuse the type invariant)
Inv == TypeOK

====