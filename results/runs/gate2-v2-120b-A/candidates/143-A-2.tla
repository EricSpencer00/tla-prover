---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Constants (the actual values are supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals
East   == "East"
West   == "West"
Banks  == {East, West}
BoatCap == 2   \* maximum boat capacity (for readability)

\* ----------------------------------------------------------------------
\* Type Definitions
\* ----------------------------------------------------------------------
BoatCanMove == {1, 2}   \* number of people that may be on the boat

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Boat, Bank

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Count the number of missionaries on a given bank
MissionariesOn(b) == Cardinality({ p \in Bank[b] : p \in Missionaries })

\* Count the number of cannibals on a given bank
CannibalsOn(b)   == Cardinality({ p \in Bank[b] : p \in Cannibals })

\* Safety condition for a single bank
BankSafe(b) == 
    /\ (MissionariesOn(b) = 0) \/ (CannibalsOn(b) <= MissionariesOn(b))

\* Global safety (both banks safe)
Safe == /\ BankSafe(East) /\ BankSafe(West)

\* Number of people on the boat must be 1 or 2
BoatSizeOK == Cardinality(Boat) \in BoatCanMove

\* The model's TYPE OK invariant (ensures proper domains)
TypeOK == 
    /\ Boat \subseteq People
    /\ BoatSizeOK
    /\ Bank \in [Banks -> SUBSET People]
    /\ /\ Bank[East] \cup Bank[West] = People
       /\ Bank[East] \cap Bank[West] = {}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ Boat = {}
    /\ Bank = [East |-> People, West |-> {}]

\* ----------------------------------------------------------------------
\* Action: Move (one or two people cross the river)
\* ----------------------------------------------------------------------
Move == 
    \/ /\ Boat = {}                               \* load the boat
       /\ Boat' = Subset \{ People \} 
                \cap { p \in Bank[BoatLoc] : p \in People }
                \cap { p \in People : p \in Missionaries \/ p \in Cannibals }
                \cap { p : p \in People }        \* any subset of current bank
       /\ Cardinality(Boat') \in BoatCanMove
       /\ UNCHANGED BoatLoc
       /\ UNCHANGED Bank
    \/ /\ Boat' = {}                               \* unload the boat at destination
       /\ BoatLoc' = IF BoatLoc = East THEN West ELSE East
       /\ Bank' = [b \in Banks |-> 
                IF b = BoatLoc' 
                THEN Bank[b] \cup Boat 
                ELSE IF b = BoatLoc 
                     THEN Bank[b] \setminus Boat 
                     ELSE Bank[b]]
       /\ Safe
       /\ BoatSizeOK
       
\* The above Move action is split into two phases for readability:
\*   1. Load: when Boat = {} we may nondeterministically pick a non‑empty
\*      subset of 1 or 2 people from the current bank.
\*   2. Unload: when Boat ≠ {} we cross to the opposite bank, empty the boat,
\*      and update the distribution of people.

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    \/ \E b \in People : 
         /\ Boat = {}
         /\ b \in Bank[BoatLoc]
         /\ Boat' = {b}
         /\ UNCHANGED Bank
         /\ UNCHANGED BoatLoc
    \/ \E b1, b2 \in People : 
         /\ Boat = {}
         /\ {b1, b2} \subseteq Bank[BoatLoc]
         /\ Boat' = {b1, b2}
         /\ UNCHANGED Bank
         /\ UNCHANGED BoatLoc
    \/ /\ Boat # {}
       /\ BoatLoc' = IF BoatLoc = East THEN West ELSE East
       /\ Bank' = [b \in Banks |-> 
                IF b = BoatLoc' 
                THEN Bank[b] \cup Boat 
                ELSE IF b = BoatLoc 
                     THEN Bank[b] \setminus Boat 
                     ELSE Bank[b]]
       /\ Boat' = {}
       /\ Safe

\* ----------------------------------------------------------------------
\* Invariant describing the solution condition (the puzzle is solved)
\* ----------------------------------------------------------------------
Solution == Bank[East] = {}

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Boat, BoatLoc, Bank>>

\* ----------------------------------------------------------------------
\* THEOREM (optional, shows that the spec implies the invariants)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====