---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS A, B, C, bound

\* The set of possible elements
ElementSet == { A, B, C }

\* Finite sequences over ElementSet with length at most bound
BoundedSeq == { s \in Seq(ElementSet) : Len(s) <= bound }

\* State variables
VARIABLES seq, i, candidate, counter

vars == << seq, i, candidate, counter >>

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ seq \in BoundedSeq
    /\ i = 1
    /\ candidate \in ElementSet
    /\ counter = 0

\* ----------------------------------------------------------------------
\* Helper: count how many times a value occurs in a sequence
Count(s, a) == Cardinality({ j \in DOMAIN s : s[j] = a })

\* ----------------------------------------------------------------------
\* The core scanning step of the Boyer‑Moore majority vote algorithm
Scan ==
    LET x == seq[i] IN
    /\ i <= Len(seq)
    /\ /\ IF counter = 0
          THEN /\ candidate' = x
               /\ counter'   = 1
       ELSE IF candidate = x
          THEN /\ candidate' = candidate
               /\ counter'   = counter + 1
       ELSE /\ candidate' = candidate
            /\ counter'   = counter - 1
    /\ i' = i + 1
    /\ UNCHANGED seq

\* When the scan is finished the system may stutter
Next ==
    \/ Scan
    \/ (i > Len(seq) /\ UNCHANGED << seq, i, candidate, counter >>)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq
    /\ i \in Nat
    /\ candidate \in ElementSet
    /\ counter \in Nat

\* ----------------------------------------------------------------------
\* Inductive invariant (strengthened type invariant)
Inv == TypeOK /\ i <= Len(seq) + 1

\* ----------------------------------------------------------------------
\* Correctness: after a complete scan, any true majority element must equal the candidate
Correct ==
    (i = Len(seq) + 1) =>
        ( \A a \in ElementSet :
            (Count(seq, a) > Len(seq) / 2) => candidate = a )

====