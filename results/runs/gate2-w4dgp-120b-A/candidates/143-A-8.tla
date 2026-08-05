---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bankSide, peopleAt

vars == <<bankSide, peopleAt>>

Banks == {"east", "west"}

Group == SUBSET Missionaries \cup Cannibals

\* The boat may only cross with 1 or 2 people aboard.
BoatLoadOK(g) == g # {} /\ Cardinality(g) <= 2

People == Missionaries \cup Cannibals

\* Safety rule of the puzzle: on any bank where a missionary is present,
\* cannibals must not outnumber them, or the mission fails (eaten).
Safe(b) ==
  LET m == Cardinality(peopleAt[b] \cap Missionaries)
      c == Cardinality(peopleAt[b] \cap Cannibals)
  IN m = 0 \/ c <= m

TypeOK ==
  /\ bankSide \in Banks
  /\ peopleAt \in [Banks -> SUBSET People]

Init ==
  /\ bankSide = "east"
  /\ peopleAt = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Next ==
  \/ \E g \in Group :
       /\ BoatLoadOK(g)
       /\ g \subseteq peopleAt[bankSide]
       /\ LET destSide == IF bankSide = "east" THEN "west" ELSE "east"
              newPeople == [peopleAt EXCEPT ![bankSide] = @ \ g,
                                          ![destSide] = @ \cup g]
          IN /\ Safe(destSide)
             /\ Safe(bankSide)
             /\ peopleAt' = newPeople
             /\ bankSide' = destSide
  \/ UNCHANGED <<bankSide, peopleAt>>

\* The puzzle is solved once the entire party has crossed.
Solution == peopleAt["east"] = {}

====