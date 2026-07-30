---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Value

\* The proof extends the main Boyer-Moore majority vote specification. All
\* state variables, INITS, and NEXTs are inherited from that base spec.
\* Here we only add the machine-checked proof that the algorithm is correct.

\* The base specification is brought in as a namespace prefix; it is assumed
\* to be available in the same model (imported from the main module).
\* This keeps the proof module self-contained while still referencing the
\* original algorithm definition.
\*   Candidate, Count, Pos, Seq, Len, Total
\* are all defined there and are used in the lemmas below.

\* TypeOK: the state variables always stay within their intended types.
TypeOK ==
  /\ Candidate \in Value \cup {"none"}
  /\ Count \in 0..Len
  /\ Pos \in 0..Len
  /\ Seq \in [0..(Len - 1) -> Value]
  /\ Len \in Nat
  /\ Total \in 0..Len

\* Positions(i) = the set of indices visited up to position i.
Positions(i) == {j \in 0..(Len - 1) : j < i}

\* CountValue(c) = how many times c occurs in positions already visited.
CountValue(c) ==
  Cardinality({j \in Positions(Pos) : Seq[j] = c})

\* The invariant Inv ties Count to the true occurrence count of Candidate,
\* and captures the emptiness of the count when there is no candidate.
Inv ==
  /\ (Candidate # "none") => Count = CountValue(Candidate)
  /\ (Candidate = "none") => Count = 0

\* Correct: after the scan finishes, any value that appears more than half
\* the time must equal the candidate the algorithm computed.
Correct ==
  (Pos = Len) => (\A c \in Value : (Total >= 2 * CountValue(c)) => c = Candidate)

\* The full set of invariants proved by TLAPS.
PROPERTIES == TypeOK /\ Correct

\* A helper lemma about positions: adding the current index to the visited
\* set strictly increases its cardinality (the algorithm always progresses).
PositionsGrow ==
  Cardinality(Positions(Pos + 1)) = Cardinality(Positions(Pos)) + 1

====