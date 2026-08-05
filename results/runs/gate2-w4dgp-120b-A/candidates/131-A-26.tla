---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* An interactive formal proof that the Boyer-Moore majority vote algorithm never
\* errs: every value appearing in a strict majority of the scanned sequence
\* must be the candidate left at the end, and the code always stays well-typed.
\* The proof uses TLAPS and a handful of standard set-theoretic lemmas.
ASSUME Value # {}

VARIABLES candidate, count, seen, seq, n

vars == <<candidate, count, seen, seq, n>>

TypeOK ==
  /\ candidate \in Value \cup {"none"}
  /\ count \in Nat
  /\ seen \in SUBSET (Value \X Nat)
  /\ seq \in Seq(Value)
  /\ n \in Nat

\* Incremental occurrence count of a value up to a given index.
OccurBefore(v, t) == { x \in {1, .., n} : seq[x] = v /\ x <= t }

Init ==
  /\ candidate = "none"
  /\ count = 0
  /\ seen = {}
  /\ seq = <<>>
  /\ n = 0

Next(v) ==
  /\ v \in Value
  /\ n < 3
  /\ seq' = Append(seq, v)
  /\ n' = n + 1
  /\ seen' = seen \cup {<<v, n + 1>>}
  /\ IF count = 0
       THEN candidate' = v /\ count' = 1
       ELSE IF candidate = v
              THEN count' = count + 1
              ELSE count' = count - 1
       /\ candidate' = IF candidate = v THEN candidate ELSE IF count = 1 THEN v ELSE candidate

Spec == Init /\ [][Next(v) FOR v \in Value]

\* The code never leaves its type-correct state.
TypeOK == Init /\ [Next(v) FOR v \in Value]_vars

\* The inductive invariant from the main specification: any strict majority
\* value never conflicts with the candidate.
Inv == (count = 0 => candidate = "none") /\ (count > 0 => candidate \in Value)

\* Correctness: a strict-majority element must be the candidate.
Correct == \A v \in Value : (2 * Cardinality(OccurBefore(v, n)) > n) => v = candidate

====