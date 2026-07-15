---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants representing the set of missionaries and the set of cannibals.
\* The .cfg file must assign concrete values to these constants.
\* ----------------------------------------------------------------------
CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived sets and a type for the two possible banks.
\* ----------------------------------------------------------------------
People      == Missionaries \cup Cannibals
Bank        == {"East", "West"}
SingleBank  == {"East", "West"}

\* ----------------------------------------------------------------------
\* State variables
\*   boat: which bank the boat is currently docked at.
\*   east, west: the set of people currently on each bank.
\* ----------------------------------------------------------------------
VARIABLES boat, east, west

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PeopleOn(b) == IF b = "East" THEN east ELSE west

CountOn(b, S) == Cardinality(PeopleOn(b) \cap S)

MissionariesOn(b) == PeopleOn(b) \cap Missionaries
CannibalsOn(b)    == PeopleOn(b) \cap Cannibals

\* Safety condition for a single bank: either no missionaries,
\* or missionaries are not outnumbered by cannibals.
\* ----------------------------------------------------------------------
BankSafe(b) == 
    LET m == CountOn(b, Missionaries) IN
    LET c == CountOn(b, Cannibals)    IN
    (m = 0) \/ (c <= m)

\* The overall safety condition: both banks must be safe.
\* ----------------------------------------------------------------------
Safe == /\ BankSafe("East")
        /\ BankSafe("West")

\* ----------------------------------------------------------------------
\* The initial state: everyone starts on the east bank, boat also on east.
\* ----------------------------------------------------------------------
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

\* ----------------------------------------------------------------------
\* Definition of a legal move: a non‑empty group of one or two people
\* boards the boat on the current bank and crosses to the opposite bank,
\* producing a new state that satisfies the safety condition.
\* ----------------------------------------------------------------------
Move ==
    \E group \in SUBSET PeopleOn(boat) :
        /\ group # {}                \* at least one person
        /\ Cardinality(group) <= 2  \* at most two persons
        /\ LET dest == IF boat = "East" THEN "West" ELSE "East" IN
           /\ boat' = dest
           /\ east' = IF boat = "East"
                     THEN east \ group
                     ELSE east \cup group
           /\ west' = IF boat = "West"
                     THEN west \ group
                     ELSE west \cup group
           /\ Safe                    \* the resulting state must be safe

\* ----------------------------------------------------------------------
\* The NEXT action allows either a Move or stuttering (needed for
\* completeness of the model).
\* ----------------------------------------------------------------------
Next == Move \/ UNCHANGED <<boat, east, west>>

\* ----------------------------------------------------------------------
\* Type correctness invariant: variables stay within their intended domains.
\* ----------------------------------------------------------------------
TypeOK ==
    /\ boat \in Bank
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

\* ----------------------------------------------------------------------
\* Solution invariant: captures the "goal reached" condition.
\* It asserts that the east bank is empty (everyone has reached the west).
\* The model checker will look for a violation of this invariant to
\* obtain a solution trace.
\* ----------------------------------------------------------------------
Solution == east = {}

\* ----------------------------------------------------------------------
\* The specification combines the initial predicate and the next-state
\* relation.  It is not required by the .cfg but is customary.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, east, west>>

\* ----------------------------------------------------------------------
\* Export the required identifiers.
\* ----------------------------------------------------------------------
INIT Init
NEXT Next
INVARIANT TypeOK
INVARIANT Solution

====