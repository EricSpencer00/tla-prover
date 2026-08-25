---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

VARIABLES boat, EastBank, WestBank

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllPeople == Missionaries \cup Cannibals

Safe(bank) ==
  (Missionaries \cap bank = {}) \/ 
  (Cardinality(Cannibals \cap bank) <= Cardinality(Missionaries \cap bank))

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ boat = "East"
  /\ EastBank = AllPeople
  /\ WestBank = {}

\* ----------------------------------------------------------------------
\* Type checking invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ boat \in {"East", "West"}
  /\ EastBank \subseteq AllPeople
  /\ WestBank \subseteq AllPeople
  /\ EastBank \cup WestBank = AllPeople
  /\ EastBank \cap WestBank = {}

\* ----------------------------------------------------------------------
\* Move action
\* ----------------------------------------------------------------------
Move ==
  \E p \subseteq (IF boat = "East" THEN EastBank ELSE WestBank) :
    /\ Cardinality(p) \in 1..2
    /\ LET newEast == IF boat = "East" THEN EastBank \ p ELSE EastBank \cup p
           newWest == IF boat = "East" THEN WestBank \cup p ELSE WestBank \ p
       IN /\ EastBank' = newEast
          /\ WestBank' = newWest
          /\ boat' = (IF boat = "East" THEN "West" ELSE "East")
          /\ Safe(newEast)
          /\ Safe(newWest)

Next == Move

\* ----------------------------------------------------------------------
\* Solution invariant (violated exactly when the puzzle is solved)
\* ----------------------------------------------------------------------
Solution == EastBank \= {}

\* ----------------------------------------------------------------------
\* The specification (not required by the .cfg but useful for completeness)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, EastBank, WestBank>>

=============================================================================