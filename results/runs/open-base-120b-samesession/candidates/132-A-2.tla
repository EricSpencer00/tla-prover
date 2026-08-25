---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible element values
ValueSet == { A, B, C }

\* Finite sequences over ValueSet whose length is at most ``bound''
BoundedSeq == { s \in Seq(ValueSet) : Len(s) <= bound }

VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* Scan actions (the three cases of the Boyer‑Moore algorithm)
\* ----------------------------------------------------------------------
Adopt ==
    /\ pos <= Len(seq)
    /\ cnt = 0
    /\ LET e == seq[pos] IN
         /\ cand' = e
         /\ cnt' = 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Inc ==
    /\ pos <= Len(seq)
    /\ cnt > 0
    /\ cand = seq[pos]
    /\ cand' = cand
    /\ cnt' = cnt + 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Dec ==
    /\ pos <= Len(seq)
    /\ cnt > 0
    /\ cand # seq[pos]
    /\ cand' = cand
    /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

Scan == Adopt \/ Inc \/ Dec

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    Scan
    \/ (pos > Len(seq) /\ UNCHANGED <<seq, pos, cand, cnt>>)

vars == <<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Scan)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Majority predicate
\* ----------------------------------------------------------------------
Majority(seq) ==
    { v \in ValueSet :
        LET cntV == Cardinality({ i \in DOMAIN seq : seq[i] = v })
        IN cntV > Len(seq) / 2 }

\* ----------------------------------------------------------------------
\* Correctness property (if a true majority exists, the final candidate equals it)
\* ----------------------------------------------------------------------
Correct ==
    /\ pos > Len(seq)
    => ( \A m \in ValueSet :
            (m \in Majority(seq) => cand = m) )

\* ----------------------------------------------------------------------
\* Inductive invariant (here we reuse TypeOK)
\* ----------------------------------------------------------------------
Inv == TypeOK

====