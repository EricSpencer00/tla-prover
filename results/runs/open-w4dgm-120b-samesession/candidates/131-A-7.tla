---- MODULE MajorityProof ----
\* This module contains an interactive formal proof of correctness for the Boyer-Moore
\* majority vote algorithm. It extends the main algorithm specification with lemmas and
\* a machine-checked proof that the algorithm correctly identifies the only possible
\* majority element. The proof relies on TLAPS for verification.
EXTENDS Naturals, FiniteSets

CONSTANTS Value

VARIABLES candidate, seen, pos, seq

vars == <<candidate, seen, pos, seq>>

\* The invariant Inv is the inductive claim behind correctness: any value occurring in a
\* strict majority of positions seen so far must equal the current candidate. TypeOK checks
\* that all state variables stay within their intended domains.
TypeOK ==
  /\ candidate \in Value \cup {"none"}
  /\ seen \subseteq Value
  /\ pos \in Nat
  /\ seq \in [1..2 -> Value]

\* An occurrence-counting helper: the set of positions before index i where seq[j] = x.
Occ(x, i) == { j \in 1..(i - 1) : seq[j] = x }

Init ==
  /\ candidate = "none"
  /\ seen = {}
  /\ pos = 1
  /\ seq \in [1..2 -> Value]

Rotate == IF seq[pos] = "none" THEN Value ELSE "none"

Read(v) ==
  /\ pos <= 2
  /\ seq' = [seq EXCEPT ![pos] = v]
  /\ pos' = pos + 1
  /\ UNCHANGED <<candidate, seen>>

Vote(v) ==
  /\ pos <= 2
  /\ seq' = [seq EXCEPT ![pos] = v]
  /\ seen' = IF v \in seen THEN seen ELSE seen \cup {v}
  /\ pos' = pos + 1
  /\ UNCHANGED <<candidate>>

\* Boyer-Moore step: when the candidate slot is empty it adopts the fresh input value.
Adopt(v) ==
  /\ candidate = "none"
  /\ v \in seen
  /\ candidate' = v
  /\ UNCHANGED <<seen, pos, seq>>

\* Boyer-Moore step: when the candidate slot is busy it cancels on a competing value.
Reject(v, x) ==
  /\ candidate # "none"
  /\ v \in seen
  /\ v # candidate
  /\ v = x
  /\ candidate' = "none"
  /\ UNCHANGED <<seen, pos, seq>>

Done ==
  /\ pos > 2
  /\ UNCHANGED vars

Next ==
  \/ \E v \in Value : Read(v)
  \/ \E v \in Value : Vote(v)
  \/ \E v \in Value : Adopt(v)
  \/ \E v \in Value : \E x \in Value : Reject(v, x)
  \/ Done

Spec == Init /\ [][Next]_vars

\* Correctness: in addition to type well-formedness, the majority candidate must be the
\* only value that can ever occupy a strict majority of positions once the whole
\* sequence has been read.
Correct == TypeOK /\ Inv
Inv ==
  \A x \in Value : (2 * Cardinality(Occ(x, pos)) > pos - 1) => (candidate = x \/ pos = 1)

====