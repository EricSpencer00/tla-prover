---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

VARIABLES seq, pos, cand, count

\* ----------------------------------------------------------------------
\* Value set of the three distinct elements
\* ----------------------------------------------------------------------
ValueSet == { A, B, C }

\* ----------------------------------------------------------------------
\* BoundedSeq replaces Seq from Sequences.
\* It is the set of all finite sequences over ValueSet whose length
\* does not exceed the constant bound.
\* ----------------------------------------------------------------------
BoundedSeq == { s \in Seq(ValueSet) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ seq \in BoundedSeq
    /\ pos = 1
    /\ cand \in ValueSet
    /\ count = 0

\* ----------------------------------------------------------------------
\* Convenience definition of the element currently examined
\* ----------------------------------------------------------------------
CurElem == IF pos <= Len(seq) THEN seq[pos] ELSE NULL

\* ----------------------------------------------------------------------
\* Next‑state relation implementing the Boyer‑Moore scan
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pos <= Len(seq)               \* still scanning
       /\ CASE CurElem = cand -> 
                /\ cand' = cand
                /\ count' = count + 1
          [] count = 0 -> 
                /\ cand' = CurElem
                /\ count' = 1
          [] OTHER -> 
                /\ cand' = cand
                /\ count' = count - 1
       /\ pos' = pos + 1
       /\ seq' = seq
    \/ /\ pos > Len(seq)                \* scan finished – stutter
       /\ UNCHANGED <<seq, pos, cand, count>>

\* ----------------------------------------------------------------------
\* Tuple of all state variables
\* ----------------------------------------------------------------------
vars == <<seq, pos, cand, count>>

\* ----------------------------------------------------------------------
\* Specification (initial condition plus always‑next)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ seq \in BoundedSeq
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ count \in Nat

\* ----------------------------------------------------------------------
\* Definition of a majority element in the current sequence
\* ----------------------------------------------------------------------
Majority(e) ==
    LET n == Len(seq) IN
    Cardinality({ i \in 1..n : seq[i] = e }) > n / 2

\* ----------------------------------------------------------------------
\* Correctness invariant: after a complete scan, any true majority
\* element must equal the candidate.
\* ----------------------------------------------------------------------
Correct ==
    IF pos = Len(seq) + 1 THEN
        \A e \in ValueSet : (Majority(e) => cand = e)
    ELSE TRUE

\* ----------------------------------------------------------------------
\* Inductive invariant (standard Boyer‑Moore invariant)
\* ----------------------------------------------------------------------
Inv ==
    /\ count >= 0
    /\ (count = 0 => cand \in ValueSet)

====