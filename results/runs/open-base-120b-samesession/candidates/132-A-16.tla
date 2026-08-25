---- MODULE MCMajority ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS A, B, C, bound

\* Assume the bound is a natural number
ASSUME bound \in Nat

\* The set of possible element values
ElemSet == { A, B, C }

\* Finite sequences over ElemSet whose length does not exceed the bound
BoundedSeq == { s \in Seq(ElemSet) : Len(s) \le bound }

VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ cand \in ElemSet
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Transition relation (scan step and stuttering after the scan)
\* ----------------------------------------------------------------------
Scan ==
    /\ i \le Len(seq)
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

Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next == Scan \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<seq, i, cand, cnt>> /\ WF_<<seq, i, cand, cnt>>(Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ cand \in ElemSet
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Helper definitions for the correctness property
\* ----------------------------------------------------------------------
Count(m) == Cardinality({ j \in 1..Len(seq) : seq[j] = m })
Majority(m) == Count(m) > Len(seq) / 2

\* ----------------------------------------------------------------------
\* Main correctness property: after a complete scan, any true majority
\* element must equal the candidate.
\* ----------------------------------------------------------------------
Correct ==
    (i > Len(seq)) => \A m \in ElemSet : (Majority(m) => cand = m)

\* ----------------------------------------------------------------------
\* An inductive invariant (simple example)
\* ----------------------------------------------------------------------
Inv ==
    TypeOK /\ i \le Len(seq) + 1

====