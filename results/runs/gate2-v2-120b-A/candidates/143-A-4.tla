---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants representing the sets of individuals
\* ----------------------------------------------------------------------
CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived constant: the universe of all people
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* State variables
\*   BoatAt : "East" or "West"
\*   East   : the set of people currently on the east bank
\*   West   : the set of people currently on the west bank
\* ----------------------------------------------------------------------
VARIABLES BoatAt, East, West

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The two possible locations for the boat
BoatSides == {"East", "West"}

\* The opposite side of a given side
OppositeSide(s) == IF s = "East" THEN "West" ELSE "East"

\* The set of people located on the same side as the boat
SameSidePeople == IF BoatAt = "East" THEN East ELSE West

\* The set of people located on the opposite side of the boat
OppositeSidePeople == IF BoatAt = "East" THEN West ELSE East

\* Safety predicate for a single bank
SafeBank(bank) ==
    LET m == Cardinality(bank \cap Missionaries) IN
    LET c == Cardinality(bank \cap Cannibals) IN
        (m = 0) \/ (c <= m)

\* Global safety condition (both banks safe)
Safe == SafeBank(East) /\ SafeBank(West)

\* ----------------------------------------------------------------------
\* Type correctness predicate (optional but required as an INVARIANT)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ BoatAt \in BoatSides
    /\ East \subseteq People
    /\ West \subseteq People
    /\ East \cup West = People
    /\ East \cap West = {}

\* ----------------------------------------------------------------------
\* Initial state
\*   - Boat at East
\*   - All people on East
\*   - West empty
\* ----------------------------------------------------------------------
Init ==
    /\ BoatAt = "East"
    /\ East = People
    /\ West = {}

\* ----------------------------------------------------------------------
\* A nondeterministic selection of a group of 1 or 2 people from the
\* current boat side, together with the crossing action.
\* ----------------------------------------------------------------------
Move ==
    \E group \in SUBSET SameSidePeople :
        /\ Cardinality(group) \in 1..2
        /\ LET newEast ==
                IF BoatAt = "East"
                THEN East \ setdiff group
                ELSE East \cup group
           IN
           LET newWest ==
                IF BoatAt = "West"
                THEN West \ setdiff group
                ELSE West \cup group
           IN
        /\ BoatAt' = OppositeSide(BoatAt)
        /\ East' = newEast
        /\ West' = newWest
        /\ Safe   \* safety must hold after the move
        /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation (only the Move action is possible)
\* ----------------------------------------------------------------------
Next == Move

\* ----------------------------------------------------------------------
\* Safety invariant required by the description
\* ----------------------------------------------------------------------
Solution == Safe

\* ----------------------------------------------------------------------
\* Specification (not strictly required by the .cfg but customary)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<BoatAt, East, West>>

\* ----------------------------------------------------------------------
\* Theorems (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []Safe

====