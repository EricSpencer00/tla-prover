---- MODULE MissionariesAndCannibals ----
\* Missionaries and cannibals must cross a river using a boat of limited capacity.
\* At no point may missionaries on a bank be outnumbered by cannibals, and the
\* boat never crosses empty.
EXTENDS Naturals, FiniteSets

Banks == {"east", "west"}

VARIABLES boatAt, bank

vars == <<boatAt, bank>>

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* The puzzle is solved once the east bank is empty (all have crossed west).
Solved == bank["east"] = {}

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
Safe(b) ==
  LET m == Cardinality(bank[b] \cap Missionaries) IN
  LET c == Cardinality(bank[b] \cap Cannibals) IN
    m = 0 \/ c <= m

\* One to two people cross from the current bank to the opposite one.
Move ==
  /\ ~Solved
  /\ \E g \in [Missionaries \cup Cannibals -> BOOLEAN] :
       /\ Cardinality(g) >= 1
       /\ Cardinality(g) <= 2
       /\ g \subseteq bank[boatAt]
       /\ LET other == (CHOOSE b \in Banks : b # boatAt) IN
            /\ bank' = [bank EXCEPT ![boatAt] = @ \ g, ![other] = @ \cup g]
            /\ boatAt' = other
  /\ Safe(boatAt)
  /\ Safe((CHOOSE b \in Banks : b # boatAt))

Next == Move

\* Explicitly name the safety property (not a TypeOK-style type-correctness
\* check) for the .cfg's INVARIANT section.
Solution == ~Solved => \A b \in Banks : Safe(b)

Spec == Init /\ [][Next]_vars

====