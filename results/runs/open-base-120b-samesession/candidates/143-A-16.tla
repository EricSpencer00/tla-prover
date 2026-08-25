---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Missionaries, \* set of the three missionaries
    Cannibals      \* set of the three cannibals

\* ----------------------------------------------------------------------
\* Derived sets
People == Missionaries \cup Cannibals
Banks  == {"East", "West"}

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    boat,   \* current dock of the boat, either "East" or "West"
    east,   \* set of people on the east bank
    west    \* set of people on the west bank

\* ----------------------------------------------------------------------
\* Helper predicates
SafeBank(b) ==
    ( Missionaries \cap b = {} ) \/
    ( Cardinality(Cannibals \cap b) <= Cardinality(Missionaries \cap b) )

CurrentBank == IF boat = "East" THEN east ELSE west
OtherBank   == IF boat = "East" THEN west ELSE east

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ boat \in Banks
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

\* ----------------------------------------------------------------------
\* Safety: both banks must be safe after every move
SafeAll ==
    /\ SafeBank(east)
    /\ SafeBank(west)

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

\* ----------------------------------------------------------------------
\* Move action (boat carries 1 or 2 people, never empty)
Move ==
    \E p \in SUBSET CurrentBank :
        /\ Cardinality(p) \in 1..2
        /\ LET newEast == IF boat = "East" THEN east \ p ELSE east \cup p
           IN LET newWest == IF boat = "East" THEN west \cup p ELSE west \ p
              IN /\ east' = newEast
                 /\ west' = newWest
                 /\ boat' = IF boat = "East" THEN "West" ELSE "East"
                 /\ SafeBank(newEast)
                 /\ SafeBank(newWest)

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    Move

\* ----------------------------------------------------------------------
\* Specification (not required by .cfg but useful)
Spec == Init /\ [][Next]_<<boat, east, west>>

\* ----------------------------------------------------------------------
\* Invariant stating that the puzzle is solved when the east bank is empty
Solution == east = {}

\* ----------------------------------------------------------------------
\* The set of invariants that the model checker must verify
THEOREM TypeOKInv ==  []TypeOK
THEOREM SolutionInv == []Solution

====