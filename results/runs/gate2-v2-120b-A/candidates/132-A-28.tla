---- MODULE MCMajority ----
EXTENDS Naturals, Sequences

\* ----------------------------------------------------------------------
\* Constants (to be instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in Seq
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Action: scan the next element (three‑case logic)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pos <= Len(seq)
       /\ LET cur == seq[pos] IN
          /\ IF cand = cur THEN
                /\ cand' = cand
                /\ cnt' = cnt + 1
             ELSE IF cnt = 0 THEN
                /\ cand' = cur
                /\ cnt' = 1
             ELSE
                /\ cand' = cand
                /\ cnt' = cnt - 1
          /\ pos' = pos + 1
          /\ seq' = seq
    \/ /\ pos > Len(seq)   \* end of scan, stay in the same state
       /\ UNCHANGED <<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Safety invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in Seq
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: correctness of majority voting
\* If an element appears more than half the time in the whole sequence
\* then after the scan (pos > Len(seq)) that element must equal the final
\* candidate.
\* ----------------------------------------------------------------------
Correct ==
    /\ pos > Len(seq)      \* scan complete
    => \A v \in Values :
          (Cardinality({ i \in 1..Len(seq) : seq[i] = v }) > Len(seq) / 2)
          => cand = v

\* ----------------------------------------------------------------------
\* Inductive invariant (the one used by the original majority vote spec)
\* It captures the relationship between the current candidate/counter and
\* the prefix of the sequence that has been processed.
\* ----------------------------------------------------------------------
Inv ==
    /\ pos \in 1..(Len(seq) + 1)
    /\ cnt \in Nat
    /\ cnt = 0 => cand \in Values
    /\ cnt > 0 => cand \in Values
    /\ LET processed == 1..pos-1 IN
       /\ cnt = Cardinality(
                { i \in processed : seq[i] = cand })
          - Cardinality(
                { i \in processed : seq[i] # cand })
          \/ (cnt = 0 /\ cand \in Values)

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Correct, Inv
====