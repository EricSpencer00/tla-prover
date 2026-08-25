---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Persons == Missionaries \cup Cannibals
Banks   == {"East", "West"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES BoatAt, East, West

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Safe(bank) ==
  LET m == Cardinality(bank \cap Missionaries) ;
      c == Cardinality(bank \cap Cannibals)
  IN (m = 0) \/ (c <= m)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ BoatAt = "East"
  /\ East = Persons
  /\ West = {}

\* ----------------------------------------------------------------------
\* Next-state relation (move action)
\* ----------------------------------------------------------------------
Next ==
  \/ \E persons \subseteq East :
        /\ BoatAt = "East"
        /\ Cardinality(persons) \in {1, 2}
        /\ LET newEast == East \ persons
               newWest == West \cup persons
           IN  /\ Safe(newEast) /\ Safe(newWest)
               /\ BoatAt' = "West"
               /\ East'   = newEast
               /\ West'   = newWest
  \/ \E persons \subseteq West :
        /\ BoatAt = "West"
        /\ Cardinality(persons) \in {1, 2}
        /\ LET newWest == West \ persons
               newEast == East \cup persons
           IN  /\ Safe(newEast) /\ Safe(newWest)
               /\ BoatAt' = "East"
               /\ East'   = newEast
               /\ West'   = newWest

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ BoatAt \in Banks
  /\ East \subseteq Persons
  /\ West \subseteq Persons
  /\ East \cap West = {}
  /\ East \cup West = Persons

\* ----------------------------------------------------------------------
\* Solution invariant (goal reached)
\* ----------------------------------------------------------------------
Solution == East = {}

====