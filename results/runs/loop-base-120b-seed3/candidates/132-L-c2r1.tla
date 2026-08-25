---- MODULE MCMajority ----
EXTENDS Naturals, Sequences, FiniteSets, Real

CONSTANTS A, B, C, bound

\* Set of possible element values
ValueSet == { A, B, C }

\* BoundedSeq(b) – the set of all (finite) sequences over ValueSet whose length ≤ b
BoundedSeq(b) == { s \in Seq(ValueSet) : Len(s) <= b }

\* State variables
VARIABLES seq, pos, cand, cnt

\* Helper to obtain the length of a sequence
SeqLen(s) == Len(s)

\* Initial state: a nondeterministic sequence of length ≤ bound,
\* scan position starts at 1, candidate arbitrary, counter zero
Init ==
    /\ seq \in BoundedSeq(bound)
    /\ pos = 1
    /\ cand \in ValueSet
    /\ cnt = 0

\* The Boyer‑Moore update step
Step ==
    /\ pos <= SeqLen(seq)
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

\* Stuttering when the scan is finished
Done ==
    /\ pos > SeqLen(seq)
    /\ UNCHANGED <<seq, pos, cand, cnt>>

Next ==
    \/ Step
    \/ Done

\* State vector
vars == <<seq, pos, cand, cnt>>

\* Specification
Spec == Init /\ [][Next]_vars

\* Type correctness invariant
TypeOK ==
    /\ seq \in BoundedSeq(bound)
    /\ pos \in Nat
    /\ cand \in ValueSet
    /\ cnt \in Nat

\* Majority definition for a given sequence
Majority(s) ==
    { v \in ValueSet :
        Cardinality({ i \in DOMAIN s : s[i] = v }) > SeqLen(s) \div 2 }

\* Correctness invariant: if a true majority exists after the scan,
\* the candidate equals that element
Correct ==
    (pos > SeqLen(seq) /\ Majority(seq) # {}) => cand \in Majority(seq)

\* Inductive invariant (can be strengthened as needed)
Inv == TypeOK

====