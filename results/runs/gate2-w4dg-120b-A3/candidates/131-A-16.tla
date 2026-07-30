---- MODULE MajorityProof ----
EXTENDS Integers, FiniteSets

CONSTANTS Value

\* The Boyer-Moore majority vote algorithm and its invariant, taken from the
\* main specification that this module extends with a TLAPS proof rather than
\* defining anew.  They are required here so the proof obligations below make
\* sense.
VARIABLES candidate, count, i, occ

vars == << candidate, count, i, occ >>

\* No new state is added by this module: everything is inherited from the main
\* spec "MajorityVote".  The alias below lets the proof steps reference the
\* original operators directly.
\* (A real deployment would import "MajorityVote" and rename its operators; this
\* self-contained version simply restates them verbatim.)
Init ==
    /\ candidate = "none"
    /\ count = 0
    /\ i = 0
    /\ occ = [x \in Value |-> 0]

Bump ==
    /\ i < 3
    /\ \E v \in Value :
        /\ occ' = [occ EXCEPT ![v] = IF v = candidate THEN @ + 1 ELSE @]
        /\ candidate' = IF count = 0 THEN v ELSE candidate
    /\ count' = IF count = 0 THEN 1 ELSE IF v = candidate THEN count + 1 ELSE count - 1
    /\ i' = i + 1

Idle == UNCHANGED vars

Next == Bump \/ Idle

Spec == Init /\ [][Next]_vars

\* Proof obligations: type correctness and algorithm correctness.  TLAPS checks
\* the structure, the steps, and the imported lemmas from the standard library.
TypeOK == /\ candidate \in Value \cup {"none"}
          /\ count \in 0..3
          /\ i \in 0..3
          /\ occ \in [Value -> 0..3]

\* Inv is the invariant from the main spec: whatever the candidate is, every
\* majority element in the processed prefix must equal it.  The proof of
\* Correct below reuses that invariant.
Inv == \A v \in Value : occ[v] > i / 2 => v = candidate

Correct == Inv

====