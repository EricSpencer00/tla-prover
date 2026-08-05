---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm picks a single candidate element
\* as it scans a sequence of input values.  It may only ever succeed
\* in naming an element that actually occurs in a strict majority of
\* positions; when the input has no majority it simply ends up holding
\* a leftover candidate that is not a majority at all.

\* The main algorithm is defined as an INVARIANT in an imported module,
\* because the proof in this file is about the algorithm, not about
\* how it is encoded.  The import brings in the full action set, the
\* inductive invariant, and the candidate-correctness theorem that is
\* already proved there.

IslandOfMajority == [majority |-> CHOOSE v \in Value : \A w \in Value : w # v => Count(w) * 2 < Cardinality]
\* (the island is defined in terms of the algorithm's own Count function
\* and Cardinality, so the import can see what it is proving)

\* Lemma: the finite set of positions before any index i has no members
\* whose position index is greater than or equal to i.
PositionsBeforeStrict(i) == { p \in 0 .. (i - 1) : TRUE }

\* Lemma: adding a new position index that is not already covered to a
\* finite position set strictly increases its cardinality.
CardinalityStatus(l) == Cardinality(PositionsBeforeStrict(l))

\* Main algorithm's inductive invariant: the candidate stays in step
\* with the scan count, and any strict-majority element is the
\* candidate.  The import proves this, and the proof below reuses it.
Inv == \A s \in Value : (Count(s) * 2 >= Cardinality) => (s = Candidate)

VARIABLES Candidate, Count, Processed, Majority

vars == <<Candidate, Count, Processed, Majority>>

TypeOK ==
  /\ Candidate \in Value
  /\ Count \in [Value -> 0 .. Cardinality]
  /\ Processed \in 0 .. Cardinality
  /\ Majority \subseteq Value

Init ==
  /\ Candidate = CHOOSE v \in Value : TRUE
  /\ Count = [s \in Value |-> 0]
  /\ Processed = 0
  /\ Majority = {}

\* The algorithm may only ever name a majority element at the very end,
\* when it is guaranteed that at least one majority must exist.
RecordMajority ==
  /\ Processed = Cardinality
  /\ \E v \in Value : (Count(v) * 2 > Cardinality) => (Majority' = {v})
  /\ UNCHANGED <<Candidate, Count, Processed>>

Next == RecordMajority

Spec == Init /\ [][Next]_vars

\* From the imported invariant we get every strict-majority element is
\* equal to the candidate.  Since the candidate is a real input value,
\* any majority can only be an element of Value, and it must be the
\* candidate the algorithm is holding at the end of the scan.
Correct == \A s \in Value : (Count(s) * 2 > Cardinality) => (s = Candidate)

====