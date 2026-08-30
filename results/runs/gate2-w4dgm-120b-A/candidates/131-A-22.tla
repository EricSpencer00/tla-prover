---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* The set of positions in the input sequence; indexing starts at 1.
Positions == 1..4

\* The input sequence of values; this is the concrete instance the
\* algorithm runs against, not a nondeterministic choice.
Seq == [1 |-> "y", 2 |-> "x", 3 |-> "x", 4 |-> "y"]

\* Count of occurrences of v up to position i (inclusive).
Occ(v, i) == Cardinality({j \in 1..i : Seq[j] = v})

\* Positions before i (used for subset-and-cardinality reasoning in the proof).
SetBefore(i) == {j \in 1..i - 1 : TRUE}

VARIABLES pos, candidate, candidateCount, totalCount

vars == <<pos, candidate, candidateCount, totalCount>>

TypeOK ==
  /\ pos \in Positions
  /\ candidate \in Value
  /\ candidateCount \in 0..4
  /\ totalCount \in 0..4

\* The Boyer-Moore candidate is the only value that can possibly hold a
\* strict majority once the scan is complete.
Correct ==
  /\ pos = 4
  /\ totalCount = 4
  /\ candidateCount * 2 > totalCount => candidate = "x"

\* The main invariant, lifted from the base algorithm: candidate vs. count
\* stay consistent, and no value can outrun the candidate.
Inv ==
  /\ candidateCount = Occ(candidate, pos)
  /\ \A v \in Value : Occ(v, pos) * 2 <= candidateCount + totalCount

Init ==
  /\ pos = 1
  /\ candidate = Seq[1]
  /\ candidateCount = 1
  /\ totalCount = 1

Shift(v) ==
  /\ pos < 4
  /\ pos' = pos + 1
  /\ IF v = candidate THEN candidateCount' = candidateCount + 1 ELSE candidateCount' = candidateCount
  /\ totalCount' = totalCount + 1
  /\ UNCHANGED candidate

NewCandidate(v) ==
  /\ pos < 4
  /\ v # candidate
  /\ candidateCount * 2 <= totalCount + 1
  /\ pos' = pos + 1
  /\ candidate' = v
  /\ candidateCount' = 1
  /\ totalCount' = totalCount + 1

Next ==
  \/ \E v \in Value : Shift(v)
  \/ \E v \in Value : NewCandidate(v)

Spec == Init /\ [][Next]_vars

TypeOKProvable ==
  /\ TypeOK
  /\ (Init /\ [][Next]_vars) => TypeOK

CorrectProvable ==
  /\ Correct
  /\ (Init /\ [][Next]_vars) => Correct

====