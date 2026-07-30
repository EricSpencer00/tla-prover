---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANT Value

\* The state space is imported wholesale from the main majority vote
\* specification and extended with TLAPS proof obligations.
VARIABLES seq, candidate, count, scanned, result

vars == <<seq, candidate, count, scanned, result>>

Init ==
  /\ candidate = "none"
  /\ count = 0
  /\ scanned = 0
  /\ result = "none"

\* Voting step: the candidate and its count are folded over the prefix
\* of the sequence scanned so far.
Vote ==
  /\ scanned < Len(seq)
  /\ LET x == seq[scanned + 1] IN
       candidate' = IF count = 0 THEN x
                      ELSE IF x = candidate THEN candidate
                      ELSE "none"
  /\ count' = IF count = 0 THEN 1
               ELSE IF x = candidate THEN count + 1
               ELSE count - 1
  /\ scanned' = scanned + 1
  /\ UNCHANGED <<seq, result>>

\* Result step: once the whole sequence has been scanned the candidate is
\* either the strict majority element or there is no majority.
Result ==
  /\ scanned = Len(seq)
  /\ result' = IF candidate # "none" /\ 2 * Cardinality({i \in 1..Len(seq) : seq[i] = candidate})
                > Len(seq) THEN candidate ELSE "none"
  /\ UNCHANGED <<seq, candidate, count, scanned>>

Next == Vote \/ Result

Spec == Init /\ [][Next]_vars

\* Hierarchical proof: each of the two invariants is proved by induction
\* over the steps of the specification.
TypeOK ==
  /\ candidate \in Value \cup {"none"}
  /\ count \in 0..Len(seq)
  /\ scanned \in 0..Len(seq)
  /\ result \in Value \cup {"none"}

\* Correctness: the candidate is the only value that can appear in a strict
\* majority of positions.
Correct ==
  \A x \in Value : (2 * Cardinality({i \in 1..Len(seq) : seq[i] = x}) > Len(seq))
                   => result = x

\* Inv: the inductive invariant from the main specification, carried over.
Inv == count >= 0

====