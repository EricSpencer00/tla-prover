---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, east, west

\* ----------------------------------------------------------------------
\* Universe of people
People == Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

\* ----------------------------------------------------------------------
\* Safety condition for a single bank
Safe(bank) ==
    LET m == Cardinality(Missionaries \cap bank)
        c == Cardinality(Cannibals \cap bank)
    IN  m = 0 \/ c <= m

\* ----------------------------------------------------------------------
\* Solution condition (the invariant that will be violated when solved)
Solution == east # {}

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

\* ----------------------------------------------------------------------
\* One crossing of the boat (moving 1 or 2 people)
Next ==
    ∃ g \in SUBSET (IF boat = "East" THEN east ELSE west) :
        /\ g /= {}
        /\ Cardinality(g) \in 1..2
        /\ LET newEast == IF boat = "East" THEN east \ g ELSE east \cup g
               newWest == IF boat = "East" THEN west \cup g ELSE west \ g
           IN /\ east' = newEast
              /\ west' = newWest
              /\ boat' = IF boat = "East" THEN "West" ELSE "East"
              /\ Safe(newEast)
              /\ Safe(newWest)

====