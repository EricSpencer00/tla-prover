---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES BoatAt, East

\* ----------------------------------------------------------------------
\* Derived sets
People == Missionaries \cup Cannibals
West   == People \ East

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
  /\ BoatAt \in {"East", "West"}
  /\ East \subseteq People

\* ----------------------------------------------------------------------
\* Safety condition for a single bank
SafeBank(b) ==
  (b \cap Missionaries = {}) \/ (Cardinality(b \cap Cannibals) <= Cardinality(b \cap Missionaries))

Safe == SafeBank(East) /\ SafeBank(West)

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ BoatAt = "East"
  /\ East   = People

\* ----------------------------------------------------------------------
\* One crossing of the boat (1 or 2 people)
MoveEast ==
  /\ BoatAt = "East"
  /\ \E grp \in SUBSET East :
        /\ grp # {}
        /\ Cardinality(grp) \in 1..2
        /\ LET newEast == East \ grp IN
              /\ BoatAt' = "West"
              /\ East'   = newEast
              /\ Safe'

MoveWest ==
  /\ BoatAt = "West"
  /\ \E grp \in SUBSET West :
        /\ grp # {}
        /\ Cardinality(grp) \in 1..2
        /\ LET newEast == East \cup grp IN
              /\ BoatAt' = "East"
              /\ East'   = newEast
              /\ Safe'

Next == MoveEast \/ MoveWest

\* ----------------------------------------------------------------------
\* Invariant that is violated when the puzzle is solved (east bank empty)
Solution == East # {}

====