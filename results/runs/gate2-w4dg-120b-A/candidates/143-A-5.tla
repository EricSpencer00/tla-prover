---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
NumMissionaries == Cardinality(Missionaries)
NumCannibals == Cardinality(Cannibals)
WestBank == {p \in People : p \in Missionaries}
Chickens == {p \in People : p \in Cannibals}

VARIABLES boatAt, bank, lastGroup

vars == <<boatAt, bank, lastGroup>>

\* Missionaries and cannibals must never be placed on the same bank in a way
\* that endangers them: whenever a bank holds missionaries, it must hold at
\* least as many missionaries as cannibals, so the cannibals cannot eat them.
\* The boat is a strict capacity-2 vessel, and it must always carry people.
\* "lastGroup" remembers the size of the most recent boat load, answered
\* separately as the "carrying-people" safety property.
SafeBank(b) == LET c == Cardinality(bank[b] \cap Chickens)
                  m == Cardinality(bank[b] \cap WestBank)
               IN m = 0 \/ c <= m

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ lastGroup \in 0..2

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ lastGroup = 0

\* A group of size 1 or 2 boards on the boat's current bank and crosses to
\* the other bank, but only when both banks stay safe afterwards.
Move(g) ==
  /\ g # {}
  /\ Cardinality(g) \in 1..2
  /\ g \subseteq bank[boatAt]
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
  /\ bank' = [bank EXCEPT ![boatAt] = bank[boatAt] \ g, ![IF boatAt = "east" THEN "west" ELSE "east"] = bank[IF boatAt = "east" THEN "west" ELSE "east"] \cup g]
  /\ lastGroup' = Cardinality(g)

Next == \E g \in SUBSET People : Move(g)

\* Safety: every bank is safe (no missionaries outnumbered by cannibals),
\* and the last boat load never carried zero or more than two people.
Solution ==
  /\ \A b \in Banks : SafeBank(b)
  /\ lastGroup \in 1..2

====