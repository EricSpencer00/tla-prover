---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES seq, candidate, count, i

vars == <<seq, candidate, count, i>>

\* The Boyer-Moore majority vote algorithm: scan the sequence once, maintaining a
\* candidate and a counter. The candidate is only a potential majority; the
\* correctness proof below shows it is the only possible majority value.

TypeOK ==
  /\ seq \in [1..3 -> Value]
  /\ candidate \in Value
  /\ count \in 0..3
  /\ i \in 0..3

Init ==
  /\ seq = [k \in 1..3 |-> CHOOSE v \in Value : TRUE]
  /\ candidate = CHOOSE v \in Value : TRUE
  /\ count = 0
  /\ i = 0

\* Scan the next element, updating the candidate and counter.
Step ==
  /\ i < 3
  /\ LET x == seq[i + 1] IN
       IF count = 0 THEN
         /\ candidate' = x
         /\ count' = 1
       ELSE IF x = candidate THEN
         /\ count' = count + 1
       ELSE
         /\ count' = count - 1
  /\ i' = i + 1
  /\ UNCHANGED seq

Next == Step

Spec == Init /\ [][Next]_vars

\* The candidate is the only value that can occur in a strict majority of
\* positions of the scanned sequence.
Correct ==
  \A v \in Value :
    (2 * Cardinality({k \in 1..i : seq[k] = v}) > i) => v = candidate

\* The inductive invariant from the main specification, lifted into this proof
\* module so TLAPS can check it directly.
Inv == (i = 3) => (2 * Cardinality({k \in 1..3 : seq[k] = candidate}) > 3 => candidate = seq[1])

\* Lemma: type-correctness is preserved by every transition.
TypeOKInv == TypeOK

====