---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* ----------------------------------------------------------------------
\* Value set of the three distinct elements
\* ----------------------------------------------------------------------
ValueSet == { A, B, C }

\* ----------------------------------------------------------------------
\* BoundedSeq replaces Seq from the Sequences module.
\* It yields only those finite sequences whose length does not exceed
\* the configured bound.
\* ----------------------------------------------------------------------
BoundedSeq(V) == { s \in Seq(V) : Len(s) <= bound }

\* ----------------------------------------------------------------------
\* Helper: count occurrences of a value in a sequence
\* ----------------------------------------------------------------------
Count(v, s) == Cardinality({ j \in DOMAIN s : s[j] = v })

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES seq, i, cand, count

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i \in Nat
  /\ cand \in ValueSet
  /\ count \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ seq \in BoundedSeq(ValueSet)
  /\ i = 1
  /\ count = 0
  /\ cand \in ValueSet

\* ----------------------------------------------------------------------
\* One step of the Boyer‑Moore scan
\* ----------------------------------------------------------------------
Scan ==
  /\ i <= Len(seq)
  /\ i' = i + 1
  /\ cand' = IF count = 0 THEN seq[i] ELSE cand
  /\ count' = IF count = 0 THEN 1
               ELSE IF cand = seq[i] THEN count + 1
               ELSE count - 1
  /\ UNCHANGED seq

\* ----------------------------------------------------------------------
\* Stuttering when the whole sequence has been scanned
\* ----------------------------------------------------------------------
Done ==
  /\ i > Len(seq)
  /\ UNCHANGED <<seq, i, cand, count>>

Next == Scan \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<seq, i, cand, count>>

\* ----------------------------------------------------------------------
\* Correctness property: any true majority element must equal the
\* candidate after the scan completes.
\* ----------------------------------------------------------------------
Correct ==
  \A v \in ValueSet :
    (Count(v, seq) > Len(seq) / 2) => (i > Len(seq) => cand = v)

\* ----------------------------------------------------------------------
\* Simple inductive invariant
\* ----------------------------------------------------------------------
Inv == (count = 0) \/ (cand \in ValueSet /\ count > 0)

\* ----------------------------------------------------------------------
\* Assumption about the bound
\* ----------------------------------------------------------------------
ASSUME bound \in Nat

====