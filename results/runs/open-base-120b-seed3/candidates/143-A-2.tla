---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES BoatAt, East, West

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Boats == {"East", "West"}

IsSafe(bank) ==
  LET m == Cardinality(bank ∩ Missionaries) IN
  LET c == Cardinality(bank ∩ Cannibals) IN
    (m = 0) \/ (c <= m)

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ BoatAt = "East"
  /\ East = Missionaries ∪ Cannibals
  /\ West = {}
  /\ BoatAt ∈ Boats
  /\ IsSafe(East)
  /\ IsSafe(West)

\* ----------------------------------------------------------------------
\* Next-state relation (one crossing)
\* ----------------------------------------------------------------------
Next ==
  \/ \E g \subseteq (IF BoatAt = "East" THEN East ELSE West) :
        /\ Cardinality(g) \in {1, 2}
        /\ LET newEast == IF BoatAt = "East" THEN East \ g ELSE East ∪ g
               newWest == IF BoatAt = "East" THEN West ∪ g ELSE West \ g
           IN /\ BoatAt' = (IF BoatAt = "East" THEN "West" ELSE "East")
              /\ East'   = newEast
              /\ West'   = newWest
              /\ IsSafe(newEast)
              /\ IsSafe(newWest)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ BoatAt ∈ Boats
  /\ East ∪ West = Missionaries ∪ Cannibals
  /\ East ∩ West = {}
  /\ IsSafe(East)
  /\ IsSafe(West)

\* ----------------------------------------------------------------------
\* Solution invariant (the east bank must remain non‑empty;
\* a violation means the puzzle is solved)
\* ----------------------------------------------------------------------
Solution == East # {}

====