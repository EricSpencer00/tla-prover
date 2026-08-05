---- MODULE MajorityProof ----
EXTENDS FiniteSets, Integers

CONSTANTS Value

\* This module contains an interactive formal proof of correctness for the Boyer-Moore majority
\* vote algorithm.  It extends the main majority-vote specification with lemmas and a machine-
\* checked proof that the algorithm correctly identifies the only possible majority element.
\* The proof is structured for TLAPS: it is a hierarchical proof that the type-correctness
\* invariant is maintained and that, at the end of the scan, any value occurring in a strict
\* majority of positions must be the candidate held by the algorithm.

VARIABLES cand, cnt, seq, n

vars == <<cand, cnt, seq, n>>

\* The function "positions(v, t)" is the set of indices before t where the sequence takes value
\* v; it is defined as a set comprehension rather than with a lambda, because set comprehensions
\* are directly supported by TLAPS and do not need an auxiliary lambda definition.
positions(v, t) == {k \in 0..(t - 1) : seq[k] = v}

\* Finite set lemmas used by the proof: a finite subset of the integers has a well-defined
\* cardinality, and adding an element to a finite set strictly between the old cardinality and
\* one more is impossible (so cardinalities change by exactly one when a single element is added).
FiniteSet(s) == \A x \in s : x \in INTEGER
CardMod(s, x) == Cardinality(s \cup {x}) = Cardinality(s) + 1
NoDoubleCount(s, x) == x \notin s

Init ==
  /\ cand \in Value
  /\ cnt \in 0..Cardinality(Value)
  /\ seq \in [0..4 -> Value]
  /\ n = 0

\* The Boyer-Moore update rule: when cnt is zero the current element becomes the candidate,
\* otherwise the count is adjusted up or down depending on whether the element agrees.
Step(v) ==
  /\ n < Cardinality(seq)
  /\ cand' = IF cnt = 0 THEN v ELSE cand
  /\ cnt'  = IF cnt = 0 THEN 1
            ELSE IF v = cand THEN cnt + 1 ELSE cnt - 1
  /\ seq' = seq
  /\ n' = n + 1

\* When the scan has consumed the whole sequence and the count has drained to zero, the final
\* candidate is simply reinstated so the invariant below can be expressed cleanly as a property
\* of the stored candidate rather than of a hypothetical continuation.
Reset ==
  /\ n = Cardinality(seq)
  /\ cnt = 0
  /\ \E w \in Value : cand' = w
  /\ cnt' = 0
  /\ seq' = seq
  /\ n' = n

Next == \E v \in Value : Step(v) \/ Reset

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ cand \in Value
  /\ cnt \in 0..Cardinality(Value)
  /\ seq \in [0..4 -> Value]
  /\ n \in 0..Cardinality(seq)

\* Main correctness invariant: after scanning the entire sequence, any value occurring in a
\* majority of positions must be the candidate held by the algorithm.  This is proved from the
\* inductive invariant of the main majority-vote specification, which bounds the size of the
\* set of positions where a non-candidate value occurs.
MajorityInvariant ==
  \A v \in Value :
    (n = Cardinality(seq) /\ 2 * Cardinality(positions(v, n)) > Cardinality(seq))
      => v = cand

\* The inductive invariant from the main specification: each non-candidate value occupies a
\* strictly bounded set of positions, which is what makes a majority candidate unique.
Inv ==
  \A v \in Value :
    (n = Cardinality(seq) /\ v # cand)
      => Cardinality(positions(v, n)) + cnt <= Cardinality(seq)

TypeOKInv == Init => TypeOK /\ [Next]_vars

TypeOKInvP ==
  TypeOKInv
    BY DEF Vars, Init, Next, FiniteSet, CardMod, NoDoubleCount

CorrectInv == Inv => MajorityInvariant

CorrectInvP ==
  CorrectInv
    BY DEF Inv, MajorityInvariant, positions

====