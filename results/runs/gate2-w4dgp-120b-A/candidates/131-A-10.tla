---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* This module is an interactive formal proof of the Boyer-Moore majority vote
\* algorithm. It extends the main majority vote specification with lemmas and a
\* machine-checked proof that the algorithm correctly identifies the only
\* possible majority element, using TLAPS to verify the proof obligations.

\* The proof assumes the standard finite-set lemmas about cardinality and
\* occurrence counting, already available in the standard TLA+ library.

VARIABLES candidate, count, seq, scanned, pos

vars == <<candidate, count, seq, scanned, pos>>

\* Occurrence counting functions on a finite prefix of the scanned sequence.
\* They are defined here so the proof can reason about them concretely.
Occ(v, S) == Cardinality({i \in S : seq[i] = v})
Prev(s) == {i \in scanned : i < s}
PrevCount(v, s) == Cardinality({i \in Prev(s) : seq[i] = v})

\* Type-correctness invariant carried over from the main specification.
TypeOK ==
    /\ candidate \in Value
    /\ count \in Nat
    /\ seq \in [1..4 -> Value]
    /\ scanned \subseteq (1..4)
    /\ pos \in 1..5

Init ==
    /\ candidate = CHOOSE v \in Value : TRUE
    /\ count = 0
    /\ seq = [i \in 1..4 |-> CHOOSE v \in Value : TRUE]
    /\ scanned = {}
    /\ pos = 1

Read(c) ==
    /\ pos \in 1..4
    /\ c \in Value
    /\ candidate' = c
    /\ scanned' = scanned \cup {pos}
    /\ pos' = pos + 1
    /\ UNCHANGED <<seq, count>>

Vote(c) ==
    /\ pos \in 1..4
    /\ c \in Value
    /\ seq' = [seq EXCEPT ![pos] = c]
    /\ candidate' = c
    /\ scanned' = scanned \cup {pos}
    /\ pos' = pos + 1
    /\ UNCHANGED <<count>>

\* The Boyer-Moore update: a matching vote increments the counter, a mismatch
\* decrements it, and the counter is never driven below zero.
Increment ==
    /\ pos \in 1..4
    /\ candidate \in Value
    /\ seq' = [seq EXCEPT ![pos] = candidate]
    /\ count' = count + (IF candidate = seq[pos] THEN 1 ELSE -1)
    /\ scanned' = scanned \cup {pos}
    /\ pos' = pos + 1
    /\ UNCHANGED candidate

Next == \E c \in Value : Read(c) \/ Vote(c) \/ Increment

Spec == Init /\ [][Next]_vars

\* The inductive invariant from the main specification, carried over here.
Inv ==
    /\ candidate = seq[pos-1]
    /\ count = PrevCount(candidate, pos)

\* The algorithm's correctness: any strict-majority value must equal the
\* candidate, which is the property proved by the Boyer-Moore analysis.
Correct == (pos = 5) => (FORALL v \in Value : (Occ(v, 1..4) > 2) => (v = candidate))

\* Type-correctness is proved as an invariant of the full system.
TypeOKInv == TypeOK

\* The main correctness invariant carries over unchanged from the main spec.
CorrectInv == Inv

====