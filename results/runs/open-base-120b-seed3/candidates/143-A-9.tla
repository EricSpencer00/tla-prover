---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES boat, east, west

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals

IsMissionary(p) == p \in Missionaries
IsCannibal(p)  == p \in Cannibals

MissionariesIn(s) == { p \in s : IsMissionary(p) }
CannibalsIn(s)    == { p \in s : IsCannibal(p) }

\* ----------------------------------------------------------------------
\* Safety predicate for a single bank
\* ----------------------------------------------------------------------
Safe(bank) ==
    ( Cardinality(MissionariesIn(bank)) = 0 )
    \/ ( Cardinality(CannibalsIn(bank)) <= Cardinality(MissionariesIn(bank)) )

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

\* ----------------------------------------------------------------------
\* Move action (one or two people cross)
\* ----------------------------------------------------------------------
Move ==
    \E move \subseteq People :
        /\ ( Cardinality(move) = 1 \/ Cardinality(move) = 2 )
        /\ move \subseteq ( IF boat = "East" THEN east ELSE west )
        LET newEast == IF boat = "East" THEN east \ move ELSE east \cup move
            newWest == IF boat = "East" THEN west \cup move ELSE west \ move
            newBoat == IF boat = "East" THEN "West" ELSE "East"
        IN /\ boat' = newBoat
           /\ east' = newEast
           /\ west' = newWest
           /\ Safe(newEast)
           /\ Safe(newWest)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Move

\* ----------------------------------------------------------------------
\* Solution predicate (all have crossed)
\* ----------------------------------------------------------------------
Solution == east = {}

\* ----------------------------------------------------------------------
\* The overall specification (optional, not required by identifiers)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, east, west>>

====