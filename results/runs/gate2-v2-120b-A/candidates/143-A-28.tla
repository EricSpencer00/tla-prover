---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Missionaries, \* set of all missionaries
    Cannibals    \* set of all cannibals

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
People   == Missionaries \cup Cannibals
NumM     == Cardinality(Missionaries)
NumC     == Cardinality(Cannibals)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    boat,   \* "East" or "West"
    east,   \* set of people currently on the east bank
    west    \* set of people currently on the west bank

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The two possible bank names
Bank == {"East", "West"}

\* The set of all admissible groups that can board the boat:
\* either one person or two distinct persons.
LegalBoatGroup == { g \in SUBSET People : Cardinality(g) \in {1, 2} }

\* Safety predicate for a given bank (set of people on that bank)
SafeBank(p) ==
    LET m == Cardinality(p \cap Missionaries) IN
    LET c == Cardinality(p \cap Cannibals) IN
        (m = 0) \/ (c <= m)

Safe == SafeBank(east) /\ SafeBank(west)

\* The set of people on the bank where the boat is currently docked
BoatDockedBank ==
    IF boat = "East" THEN east ELSE west

\* The set of people on the opposite bank
OppositeBank ==
    IF boat = "East" THEN west ELSE east

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Move ==
    \E g \in LegalBoatGroup :
        /\ g \subseteq BoatDockedBank           \* only people present can board
        /\ LET newEast ==
                IF boat = "East"
                THEN east \ g
                ELSE east \cup g
           IN
           LET newWest ==
                IF boat = "West"
                THEN west \ g
                ELSE west \cup g
           IN
           /\ east' = newEast
           /\ west' = newWest
           /\ boat' = IF boat = "East" THEN "West" ELSE "East"
           /\ Safe

Next == Move

\* ----------------------------------------------------------------------
\* Type correctness invariant (helps TLC)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ boat \in Bank
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

\* ----------------------------------------------------------------------
\* Solution invariant (the invariant the cfg expects)
\* ----------------------------------------------------------------------
Solution == east = {}

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, east, west>>

\* ----------------------------------------------------------------------
\* THEOREM (optional, not required by the cfg but useful)
\* ----------------------------------------------------------------------
THEOREM Spec => []Safe

====