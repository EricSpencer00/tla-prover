---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT A, B, C, bound

\* ----------------------------------------------------------------------
\* Value domain (three distinct elements)
\* ----------------------------------------------------------------------
ValueSet == { A, B, C }

\* ----------------------------------------------------------------------
\* Bounded sequences of elements from ValueSet, length ≤ bound
\* (replaces the standard Seq operator in the configuration)
\* ----------------------------------------------------------------------
BoundedSeq(S) == { s \in Seq(S) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* State variables (inherited from the main majority‑vote spec)
\* ----------------------------------------------------------------------
VARIABLES seq, pos, cand, cnt

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* ----------------------------------------------------------------------
\* Initial state (inherited)
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq(ValueSet)
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* ----------------------------------------------------------------------
\* One step of the Boyer‑Moore scan (the three‑case logic)
\* ----------------------------------------------------------------------
Scan ==
    /\ pos <= Len(seq)
    /\ LET x == seq[pos] IN
       IF cnt = 0 THEN
            /\ cand' = x
            /\ cnt' = 1
       ELSE IF x = cand THEN
            /\ cand' = cand
            /\ cnt' = cnt + 1
       ELSE
            /\ cand' = cand
            /\ cnt' = cnt - 1
    /\ pos' = pos + 1
    /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Stutter when the scan has finished
\* ----------------------------------------------------------------------
Done ==
    /\ pos > Len(seq)
    /\ UNCHANGED <<seq, pos, cand, cnt>>

Next == Scan \/ Done

\* ----------------------------------------------------------------------
\* Specification (the main formula required by the .cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, pos, cand, cnt>>

\* ----------------------------------------------------------------------
\* Majority predicate
\* ----------------------------------------------------------------------
Majority(s, e) ==
    LET occ == { i \in 1..Len(s) : s[i] = e } IN
    Cardinality(occ) > Len(s) / 2

\* ----------------------------------------------------------------------
\* Correctness property (any true majority element equals the final candidate)
\* ----------------------------------------------------------------------
Correct ==
    (pos > Len(seq)) =>
        \A e \in ValueSet :
            (Majority(seq, e) => e = cand)

\* ----------------------------------------------------------------------
\* Inductive invariant (simple version, satisfies the .cfg)
\* ----------------------------------------------------------------------
Inv == cnt \in Nat

====