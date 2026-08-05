---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

VARIABLES seq, i, cand, count
vars == <<seq, i, cand, count>>

\* seq[i] is the value at position i; i ranges from 1 to Len (the scan is 1-indexed).
\* cand/count are the Boyer-Moore candidate and vote count for the scanned prefix.

Len == 3

\* positions before index i in the scanned prefix; used for counting occurrences.
Positions(i) == {j \in 1..Len : j < i}

TypeOK ==
  /\ seq \in [1..Len -> Value]
  /\ i \in 0..(Len + 1)
  /\ cand \in Value
  /\ count \in 0..Len

\* No majority before the scan is complete; the final candidate is the unique
\* majority (if one exists, which in this bound it always does) once i passes Len.
Correct ==
  /\ Len >= 3 => \A v \in Value : (2 * Cardinality({j \in 1..Len : seq[j] = v}) > Len) => v = cand

\* The Boyer-Moore update equations are mutually exclusive and exhaustive over Pos:
\* - reset on a vote with no candidate; - keep/cancel on a match; - replace on a
\*   vote against the candidate; - idle once the scan is past the end.
\* The nesting mirrors the hierarchical proof structure in the .proof section.
\* The final case has no \A; it is the only one that applies when i = Len+1.
\A v \in Value :
  /\ (i <= Len /\ count = 0 /\ cand' = v /\ count' = 1 /\ i' = i + 1)
  \/ (i <= Len /\ count >= 1 /\ seq[i] = cand /\ cand' = cand /\ count' = count + 1 /\ i' = i + 1)
  \/ (i <= Len /\ count >= 1 /\ seq[i] # cand /\ cand' = cand /\ count' = count - 1 /\ i' = i + 1)
  \/ (i > Len /\ cand' = cand /\ count' = count /\ i' = i)

Inv == i <= Len => count >= 1

Init ==
  /\ seq \in [1..Len -> Value]
  /\ i = 0
  /\ cand = CHOOSE c \in Value : TRUE
  /\ count = 0

Next == \E v \in Value : \A x \in Vars : x' = (v \A x \in Vars : x)

Spec == Init /\ [vars -> Next] /\ WF_vars(\E v \in Value : \A x \in Vars : x' = (v \A x \in Vars : x))

PositionsIsFinite == Positions(i) \in FINITE

\* Adding a single new index k to a finite set of earlier positions adds exactly
\* one element to the occurrence count (cardinality).
AddSingleElement ==
  \A i \in 1..(Len + 1) :
    \A k \in 1..Len :
      (k < i /\ k \notin Positions(i)) =>
        Cardinality({j \in Positions(i) \cup {k} : seq[j] = seq[k]}) = Cardinality({j \in Positions(i) : seq[j] = seq[k]}) + 1

\* A value and its complement partition all positions; with count=0 the candidate
\* appears no more often than any other value in the prefix scanned so far.
ComplementCountBound ==
  \A i \in 1..(Len + 1) : \A v \in Value :
    (count = 0 /\ i <= Len) =>
      Cardinality({j \in Positions(i) : seq[j] = v}) <= Cardinality({j \in Positions(i) : seq[j] # v})

\* The candidate's final count dominates every other value's final count.
CandidateDominates ==
  \A i \in 1..(Len + 1) : \A v \in Value : count > 0 => Cardinality({j \in Positions(i) : seq[j] = v}) <= count

\* With a strict majority (count > 0 at the scan's end), the candidate is the only
\* value that can dominate. This is the core correctness claim of the algorithm.
MajorityUnique == \A i \in 1..(Len + 1) : \A v \in Value : (count > 0 /\ Cardinality({j \in Positions(i) : seq[j] = v}) * 2 > Len) => v = cand

====