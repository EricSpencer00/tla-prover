---- MODULE MajorityProof ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANT Value

\* ----------------------------------------------------------------------
\* Import the main majority‑vote specification.  It is assumed to define
\* the state variables \c candidate , \c count , \c i , and \c seq,
\* as well as the actions \c Init and \c Next.
\* ----------------------------------------------------------------------
INSTANCE Majority

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_{<<candidate, count, i, seq>>}

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ candidate \in Value \/ candidate = "None"
    /\ count \in Nat
    /\ i \in Nat
    /\ seq \in Seq(Value)

\* ----------------------------------------------------------------------
\* Helper definition: the (unique) majority element of a sequence,
\* if one exists.
\* ----------------------------------------------------------------------
MajorityElement(s) ==
    CHOOSE x \in Value :
        Cardinality({j \in 1..Len(s) : s[j] = x}) > Len(s) / 2

\* ----------------------------------------------------------------------
\* Main correctness invariant
\* ----------------------------------------------------------------------
Correct ==
    (i = Len(seq) => candidate = MajorityElement(seq))

\* ----------------------------------------------------------------------
\* Combined invariant (used by TLAPS proofs)
\* ----------------------------------------------------------------------
Inv == TypeOK /\ Correct

====