---- MODULE MCMajority ----
EXTENDS Sequences, Naturals, FiniteSets

CONSTANT A, B, C, bound

\* ----------------------------------------------------------------------
\* Value set of the elements that may appear in the input sequence
\* ----------------------------------------------------------------------
Values == { A, B, C }

\* ----------------------------------------------------------------------
\* BoundedSeq(S) is the set of all finite sequences over S whose length
\* does not exceed the constant bound.
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Count(s, v) == Cardinality({ j \in DOMAIN s : s[j] = v })

MajorityExists(s) == \E v \in Values : Count(s, v) > Len(s) / 2

MajorityElement(s) == CHOOSE v \in Values : Count(s, v) > Len(s) / 2

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(Values)
    /\ i \in Nat
    /\ cand \in Values
    /\ cnt \in Nat
    /\ i >= 1
    /\ i <= Len(seq) + 1

\* ----------------------------------------------------------------------
\* Inductive invariant (a simple strengthening of TypeOK)
\* ----------------------------------------------------------------------
Inv == 
    /\ TypeOK
    /\ cnt >= 0
    /\ i >= 1
    /\ i <= Len(seq) + 1

\* ----------------------------------------------------------------------
\* Correctness property: after a complete scan, any true majority element
\* must equal the final candidate.
\* ----------------------------------------------------------------------
Correct ==
    (i > Len(seq)) => (MajorityExists(seq) => cand = MajorityElement(seq))

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(Values)
    /\ i = 1
    /\ cand \in Values
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* The scanning step of the Boyer‑Moore algorithm
\* ----------------------------------------------------------------------
Scan ==
    /\ i <= Len(seq)
    /\ LET cur == seq[i] IN
       IF cnt = 0 THEN
          /\ cand' = cur
          /\ cnt' = 1
          /\ i' = i + 1
       ELSE IF cur = cand THEN
          /\ cand' = cand
          /\ cnt' = cnt + 1
          /\ i' = i + 1
       ELSE
          /\ cand' = cand
          /\ cnt' = cnt - 1
          /\ i' = i + 1

\* ----------------------------------------------------------------------
\* No‑op step after the scan is finished (allows stuttering)
\* ----------------------------------------------------------------------
Done ==
    /\ i > Len(seq)
    /\ UNCHANGED <<seq, i, cand, cnt>>

Next ==
    Scan \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
\* (already defined as Spec)

\* INVARIANTS
\* (already defined as TypeOK, Correct, Inv)

====