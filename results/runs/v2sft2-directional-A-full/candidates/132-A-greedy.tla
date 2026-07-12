---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound, Seq

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Values == {A, B, C}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* All sequences of length up to bound over Values
AllSeqs == { s \in Seq : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in AllSeqs
    /\ pos = 1
    /\ cand \in Values
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == IF pos <= Len(seq) THEN seq[pos] ELSE NULL IN
       IF pos > Len(seq) THEN
           UNCHANGED <<seq, pos, cand, cnt>>
       ELSE
           IF x = cand THEN
               /\ pos' = pos + 1
               /\ cnt' = cnt + 1
               /\ UNCHANGED <<cand>>
           ELSE
               IF cnt = 0 THEN
                   /\ pos' = pos + 1
                   /\ cand' = x
                   /\ cnt' = 1
               ELSE
                   /\ pos' = pos + 1
                   /\ cnt' = cnt - 1
                   /\ UNCHANGED <<cand>>
\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Scan

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in AllSeqs
    /\ pos \in Nat
    /\ cand \in Values
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Correctness invariant: if a value appears more than half the time,
\* then it must be the candidate after a full scan
\* ----------------------------------------------------------------------
Correct ==
    \A v \in Values :
        ( (Len(seq) > 0) /\ (Count(v, seq) > Len(seq) / 2) ) => (cand = v)

\* ----------------------------------------------------------------------
\* Inductive invariant (the same as Correct for this model)
\* ----------------------------------------------------------------------
Inv == Correct

\* ----------------------------------------------------------------------
\* Safety properties (declared as invariants)
\* ----------------------------------------------------------------------
Safety == TypeOK /\ Correct

\* ----------------------------------------------------------------------
\* Liveness property: the scan eventually completes (weak fairness)
\* ----------------------------------------------------------------------
ScanComplete ==
    WF_0 Scan

====