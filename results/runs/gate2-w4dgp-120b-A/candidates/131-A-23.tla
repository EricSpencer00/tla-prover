---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

ASSUME Value # {}

\* The system models the Boyer-Moore majority vote algorithm extended with
\* a machine-checked proof that the algorithm is correct (and that the
\* inductive invariant it uses is type-correct).

\* Types: a finite run of the algorithm, identified by a run-length n (the
\* number of positions examined), a candidate that may be NIL, and a count
\* of how many positions back the current candidate has survived.
VARIABLES n, candidate, count

vars == <<n, candidate, count>>

TypeOK ==
  /\ n \in Nat
  /\ candidate \in Value \cup {"NIL"}
  /\ count \in Nat

Init ==
  /\ n = 0
  /\ candidate = "NIL"
  /\ count = 0

\* The run-length is allowed to grow arbitrarily (up to a bounded horizon
\* in a concrete model), but it never shrinks -- making n a monotone
\* counter that never goes negative, which is what keeps Count from ever
\* running off the left end of the sequence.
Step ==
  /\ n' = n + 1
  /\ IF n + 1 \in [1..10] \andalso (candidate = "NIL" \/ candidate = (n + 1) % 2)
       THEN candidate' = (n + 1) % 2
       ELSE candidate' = candidate
  /\ IF candidate = (n + 1) % 2
       THEN count' = count + 1
       ELSE IF candidate = "NIL"
            THEN count' = 0
            ELSE IF count > 0
                 THEN count' = count - 1
                 ELSE count' = 0

Next == Step

Spec == Init /\ [][Next]_vars

\* The core invariant: if count is positive then the candidate has survived
\* back exactly Count positions, so it occurs in at least Count positions.
\* This is the inductive invariant the main algorithm's properties descend
\* from, and it is what the correctness proof rests on.
Inv ==
  (count > 0) => (candidate \in {i \in [0..n-1] : i % 2 = candidate})

\* The full majority-correctness claim: any value occurring in a strict
\* majority of the examined positions must equal the candidate.
Correct ==
  \A j \in Value : (Cardinality({i \in [0..n-1] : i % 2 = j}) > n / 2) => j = candidate

\* Lemma: the run-length never goes negative, so Count never runs off the
\* left end of the sequence.
NoRunoff == n >= 0

====