---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS A, B, C, bound

\* ----------------------------------------------------------------------
\* Value domain
\* ----------------------------------------------------------------------
ValueSet == { A, B, C }

\* ----------------------------------------------------------------------
\* Bounded sequences (finite version of Seq)
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s \in [1..n -> S] : n \in 0..bound }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper: length of a bounded sequence
\* ----------------------------------------------------------------------
Len(s) == IF DOMAIN s = {} THEN 0 ELSE Cardinality(DOMAIN s)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* The Boyer‑Moore scan step
\* ----------------------------------------------------------------------
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
         IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
         ELSE IF cand = x THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
         ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Stutter when the scan is finished
\* ----------------------------------------------------------------------
Stutter ==
    /\ pos > Len(seq)
    /\ UNCHANGED << seq, pos, cand, cnt >>

Next == Scan \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

Correct ==
    /\ pos > Len(seq)
    /\ (\E m \in ValueSet :
           Cardinality({ i \in DOMAIN seq : seq[i] = m }) > Len(seq) / 2)
       => cand = 
          CHOOSE m \in ValueSet :
              Cardinality({ i \in DOMAIN seq : seq[i] = m }) > Len(seq) / 2

Inv == TypeOK

====