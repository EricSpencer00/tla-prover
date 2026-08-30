---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* A crossing ship is a non-empty group of at most two people.  People are
\* represented by a union of the missionary and cannibal participant sets.
Ship == SUBSET (Missionaries \cup Cannibals)

VARIABLES dock, peopleAt

vars == <<dock, peopleAt>>

TypeOK ==
  /\ dock \in {"east", "west"}
  /\ peopleAt \in [Bank -> SUBSET (Missionaries \cup Cannibals)]

Init ==
  /\ dock = "east"
  /\ peopleAt = [b \in {"east", "west"} |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* Safe: no missionaries outnumbered by cannibals on either bank.
\* A bank with zero missionaries is automatically safe.
Safe ==
  /\ \A b \in {"east", "west"}:
       \A m \in Missionaries:
         (m \in peopleAt[b]) => (Cardinality(peopleAt[b] \cap Cannibals) <= Cardinality(peopleAt[b] \cap Missionaries))
  /\ \A b \in {"east", "west"}:
       (Cardinality(peopleAt[b] \cap Missionaries) = 0) \/ (Cardinality(peopleAt[b] \cap Cannibals <= Cardinality(peopleAt[b] \cap Missionaries))

Move ==
  /\ \E group \in Ship:
       /\ group \subseteq peopleAt[dock]
       /\ 2 >= Cardinality(group) >= 1
       /\ (peopleAt' = [peopleAt EXCEPT ![dock] = @ \ group, ![IF dock = "east" THEN "west" ELSE "east"] = @ \cup group])
  /\ dock' = IF dock = "east" THEN "west" ELSE "east"

Next == Move

\* Progress: the simple completion test (east bank empty) is kept separate
\* from the type/invariant check so TLC's counterexample can show the full
\* solution trace (the invariant alone would swallow it).
Solution == \A b \in {"east", "west"}: peopleAt[b] = {}

TypeOK == TypeOK
\* Two separate invariants bound the shared shared state.  The second is
\* technically implied by the first two but is retained for readability.
Solution == Solution

Spec == Init /\ [][Next]_vars

====