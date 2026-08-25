---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* ----------------------------------------------------------------------
\* BoundedSeq replaces the unbounded Seq from the Sequences module.
\* It restricts sequences to length at most the constant `bound`.
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ValueSet == {A, B, C}

Count(s, v) == Cardinality({ i \in DOMAIN s : s[i] = v })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* The scanning step of the Boyer‑Moore algorithm
\* ----------------------------------------------------------------------
ScanStep ==
    LET n == Len(seq) IN
    /\ pos <= n
    LET e == seq[pos] IN
    /\ IF cnt = 0 THEN
          /\ cand' = e
          /\ cnt'  = 1
       ELSE IF e = cand THEN
          /\ cand' = cand
          /\ cnt'  = cnt + 1
       ELSE
          /\ cand' = cand
          /\ cnt'  = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* When the scan is finished we allow stuttering
\* ----------------------------------------------------------------------
Done ==
    /\ pos > Len(seq)
    /\ UNCHANGED <<seq, pos, cand, cnt>>

Next == ScanStep \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Invariants required by the configuration
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat
    /\ (pos <= Len(seq) => seq[pos] \in ValueSet)

Correct ==
    /\ pos > Len(seq)
    => \A m \in ValueSet : (Count(seq, m) > Len(seq) / 2) => cand = m

Inv == TRUE

====