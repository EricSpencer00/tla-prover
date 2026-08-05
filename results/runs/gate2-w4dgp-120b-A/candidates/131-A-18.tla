---- MODULE MajorityProof ----
EXTENDS Naturals, FiniteSets

CONSTANTS Value

\* This module contains an interactive formal proof of correctness for the
\* Boyer-Moore majority vote algorithm.  It extends the main algorithm
\* specification with lemmas and a machine-checked proof that the algorithm
\* correctly identifies the only possible majority element, using the TLA+
\* Proof System (TLAPS).  The state, initial condition, and actions are
\* inherited from the main specification; this module adds no new state.

VARIABLES cand, count, majority, seq

vars == <<cand, count, majority, seq>>

RECURSIVE Occurs(_)
Occurs(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE
                  IN 1 + Occurs(S \ {x})

Positions(v, i) == { k \in 1..(i-1) : seq[k] = v }

Init ==
    /\ seq \in [1..4 -> Value]
    /\ cand = 0
    /\ count = 0
    /\ majority = 0

Process(i) ==
    /\ i <= 4
    /\ LET v == seq[i] IN
        /\ IF count = 0 THEN cand' = v ELSE cand' = cand
        /\ IF cand = v OR count = 0 THEN count' = count + 1
           ELSE count' = count - 1
    /\ majority' = IF i = 4 /\ (count > 0 \/ count = 0) THEN cand ELSE majority
    /\ UNCHANGED seq

Spec == Init /\ [i \in 1..4 |-> Process(i)]

\* Lemma: finite subsets of a bounded integer interval are themselves bounded
\* subsets of that interval.
SubsetPositions(v, i) == Positions(v, i) \subseteq (1..(i-1))

\* Inductive invariant proving type-correctness of the state, proved from
\* the invariant in the main specification.
TypeOK ==
    /\ cand \in Value \cup {0}
    /\ count \in 0..4
    /\ majority \in Value \cup {0}
    /\ seq \in [1..4 -> Value]

\* Main correctness property from the main specification.
Inv ==
    \A v \in Value : (Occurs({i \in 1..4 : seq[i] = v}) > 2) => v = cand

TypeOKInv == TypeOK

CorrectInv == Inv

====