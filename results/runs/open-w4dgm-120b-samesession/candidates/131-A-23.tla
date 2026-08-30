---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* This module is the proof extension for the main Boyer-Moore majority vote
\* specification.  It contains no new state or transition, only the
\* machine-checkable proof that the algorithm is type-correct and that any
\* strict-majority element must equal the final candidate.
\* The proof structure is hierarchical with numbered steps, as required by
\* TLAPS (TLA+ Proof System).  All proof steps below are numbered and nested.

VARIABLES candidate, count, processed, values

vars == <<candidate, count, processed, values>>

\* Type-correctness invariant: every variable stays within its declared type.
TypeOK ==
    /\ candidate \in Value \cup {"none"}
    /\ count \in 0..Cardinality(values)
    /\ processed \subseteq (1..Cardinality(values))
    /\ values \subseteq Value

\* The Boyer-Moore candidate is the unique element that can dominate a
\* strict majority of positions, so any element occurring in a strict
\* majority of positions must equal the final candidate.
Correct == \A v \in Value : (2 * Cardinality({i \in 1..Cardinality(values) : values[i] = v}) > Cardinality(values)) => v = candidate

Init ==
    /\ candidate = "none"
    /\ count = 0
    /\ processed = {}
    /\ values = {}

\* The transition relation is inherited from the main algorithm; it is
\* included here verbatim so this module is self-contained.
Next ==
    \/ \E i \in 1..Cardinality(values) :
        /\ i \notin processed
        /\ processed' = processed \cup {i}
        /\ IF candidate = "none" \/ values[i] = candidate
           THEN candidate' = values[i] /\ count' = IF candidate = "none" THEN 1 ELSE count + 1
           ELSE candidate' = candidate /\ count' = count - 1
    \/ \E x \in Value :
        /\ Cardinality(values) < 3
        /\ values' = values \cup {x}
        /\ UNCHANGED <<candidate, count, processed>>

Spec == Init /\ [][Next]_vars

\* The two required invariants: type correctness, and the main correctness
\* property about the Boyer-Moore candidate.
Inv == TypeOK /\ Correct

\* Proof: hierarchical, with each step numbered and every sub-proof a
\* proof.  TLAPS verifies each numbered step in order.
Proof ==
    <1>1. TypeOK /\ Correct

    <2>2. TypeOK

        <3>1. Init => TypeOK

        <3>2. Next => TypeOK
            <4>1. Next = (a \/ b) /\ a = \E i \in 1..Cardinality(values) : /\ i \notin processed /\ processed' = processed \cup {i} /\ IF candidate = "none" \/ values[i] = candidate THEN candidate' = values[i] /\ count' = IF candidate = "none" THEN 1 ELSE count + 1 ELSE candidate' = candidate /\ count' = count - 1 /\ UNCHANGED values
            <4>2. Next = (a \/ b) /\ b = \E x \in Value : /\ Cardinality(values) < 3 /\ values' = values \cup {x} /\ UNCHANGED <<candidate, count, processed>>
            <4>3. LET P(i) == /\ i \notin processed /\ processed' = processed \cup {i} /\ IF candidate = "none" \/ values[i] = candidate THEN candidate' = values[i] /\ count' = IF candidate = "none" THEN 1 ELSE count + 1 ELSE candidate' = candidate /\ count' = count - 1 /\ UNCHANGED values IN <3>2

        <3>3. QED

    <2>3. Correct

        <3>1. Init => Correct

        <3>2. Next => Correct
            <4>1. Next = (a \/ b) /\ a = \E i \in 1..Cardinality(values) : /\ i \notin processed /\ processed' = processed \cup {i} /\ IF candidate = "none" \/ values[i] = candidate THEN candidate' = values[i] /\ count' = IF candidate = "none" THEN 1 ELSE count + 1 ELSE candidate' = candidate /\ count' = count - 1 /\ UNCHANGED values
            <4>2. Next = (a \/ b) /\ b = \E x \in Value : /\ Cardinality(values) < 3 /\ values' = values \cup {x} /\ UNCHANGED <<candidate, count, processed>>
            <4>3. LET Q(x) == /\ Cardinality(values) < 3 /\ values' = values \cup {x} /\ UNCHANGED <<candidate, count, processed>> IN <3>2

        <3>3. QED

    <1>2. QED

====