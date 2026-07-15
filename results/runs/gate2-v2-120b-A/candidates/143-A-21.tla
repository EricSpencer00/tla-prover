---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

\* The set of all people
People == Missionaries \cup Cannibals

\* Banks
Banks == {"East", "West"}

VARIABLES boat, east, west

\* Helper definitions
(* The people on the east bank are stored in variable east;
   the people on the west bank are given by west == People \ east *)
WestSet == People \ east

\* Types for TypeOK invariant
TypeOK == 
    /\ boat \in Banks
    /\ east \subseteq People
    /\ west = WestSet
    /\ east \cup west = People
    /\ east \cap west = {}

\* Safety condition for a given bank's population
BankSafe(s) == 
    (Cardinality({p \in s : p \in Missionaries}) = 0) \/ 
    (Cardinality({p \in s : p \in Cannibals}) <= Cardinality({p \in s : p \in Missionaries}))

\* Global safety invariant
Safety == BankSafe(east) /\ BankSafe(west)

Solution == ~("East" \in boat) /\ east = {}

\* Initial state: everyone on East, boat on East
Init == 
    /\ boat = "East"
    /\ east = People
    /\ west = {}

\* Determine the board side (the side where the boat currently is)
BoardSide == IF boat = "East" THEN "East" ELSE "West"

\* Determine the opposite bank
OppositeBank(b) == IF b = "East" THEN "West" ELSE "East"

\* Choose a non‑empty group of 1 or 2 people from the current bank,
\* then move them to the opposite bank.
Move == 
    \E g \in SUBSET (IF boat = "East" THEN east ELSE west) :
        /\ g # {}
        /\ Cardinality(g) \in 1..2
        /\ LET newEast == 
                IF boat = "East" 
                THEN east \ g 
                ELSE east \cup g
           IN
           LET newWest == People \ newEast IN
           /\ SafeAfterMove(newEast, newWest)
        /\ boat' = OppositeBank(boat)
        /\ east' = newEast
        /\ west' = newWest

\* Safety after performing a move
SafeAfterMove(e, w) == BankSafe(e) /\ BankSafe(w)

\* NEXT relation: either a Move or stuttering (to avoid deadlock)
Next == 
    \/ Move
    \/ UNCHANGED <<boat, east, west>>

\* Full specification (for completeness, though not required by .cfg)
Spec == Init /\ [][Next]_<<boat, east, west>>

=============================================================================