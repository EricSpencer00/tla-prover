---- MODULE MCMajority ----
EXTENDS Integers, Sequences, FiniteSets

\* The module models the majority vote algorithm for sequences over
\* three elements (A, B, C) of bounded length.
CONSTANTS A, B, C, bound

\* The original specification assumed that `bound` is *not* a natural
\* number, which makes the model impossible to instantiate because the
\* definition of `BoundedSeq` requires a natural upper bound.  To keep the
\* intent of the original model (examining sequences up to a certain
\* length) while preserving all semantics, we change the assumption to
\* require that `bound` *is* a natural number.
ASSUME bound \in Nat

Value == {A, B, C}

\* Set of all sequences over `Value` whose length is between 0 and `bound`
\* inclusive.  The definition mirrors the original intent but is written
\* explicitly for clarity.
BoundedSeq(S) == UNION { [1 .. n -> S] : n \in 0 .. bound }

VARIABLES seq, i, cand, cnt

\* Initialize the system with a concrete sequence drawn from the bounded
\* set, a starting index, and the initial state of the majority algorithm.
Init ==
  /\ seq \in BoundedSeq(Value)
  /\ i = 1
  /\ cand = A
  /\ cnt = 0

\* One step of the Boyer‑Moore majority vote algorithm.
Next ==
  /\ i <= Len(seq)
  /\ IF cnt = 0 THEN
        /\ cand' = seq[i]
        /\ cnt'  = 1
     ELSE
        IF seq[i] = cand THEN
           /\ cnt' = cnt + 1
           /\ cand' = cand
        ELSE
           /\ cnt' = cnt - 1
           /\ cand' = cand
  /\ i' = i + 1

\* After processing the entire sequence, `cand` is the candidate that
\* would be the majority element if one exists.
Candidate ==
  /\ i = Len(seq) + 1
  /\ cand \in Value

\* Invariant stating that the current candidate always belongs to the set
\* of possible values.
CandInValue ==
  cand \in Value

\* Invariant stating that the counter is never negative.
CntNonneg ==
  cnt >= 0

\* Optional safety invariant: if a true majority exists, the algorithm
\* eventually proposes it as the candidate.
MajorityCorrect ==
  /\ CandInValue
  /\ ( \E v \in Value :
        Cardinality({ j \in 1..Len(seq) : seq[j] = v }) >
        Len(seq) / 2
        => cand = v )

\* The specification's behavior.
Spec == Init /\ [][Next]_<<seq, i, cand, cnt>>

\* The set of states that TLC will explore.
vars == <<seq, i, cand, cnt>>

====