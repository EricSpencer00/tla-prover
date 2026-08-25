---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES boat, east, west

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Bank == {"East", "West"}

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

Safe(bankPeople) ==
  \/ bankPeople \cap Missionaries = {}
  \/ Cardinality(bankPeople \cap Cannibals) <= Cardinality(bankPeople \cap Missionaries)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ boat = "East"
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

\* ----------------------------------------------------------------------
\* Move action (boat carries 1 or 2 people, never empty)
\* ----------------------------------------------------------------------
Move ==
  \/ \* Boat is on the East bank, people move to West
     /\ boat = "East"
     /\ \E grp \in SUBSET(east) :
          /\ Cardinality(grp) \in 1..2
          /\ boat' = "West"
          /\ east' = east \ grp
          /\ west' = west \cup grp
          /\ Safe(east')
          /\ Safe(west')
  \/ \* Boat is on the West bank, people move to East
     /\ boat = "West"
     /\ \E grp \in SUBSET(west) :
          /\ Cardinality(grp) \in 1..2
          /\ boat' = "East"
          /\ west' = west \ grp
          /\ east' = east \cup grp
          /\ Safe(east')
          /\ Safe(west')

Next == Move

\* ----------------------------------------------------------------------
\* Type correctness and safety invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ boat \in Bank
  /\ east \subseteq Missionaries \cup Cannibals
  /\ west \subseteq Missionaries \cup Cannibals
  /\ east \cup west = Missionaries \cup Cannibals
  /\ east \cap west = {}
  /\ Safe(east)
  /\ Safe(west)

\* ----------------------------------------------------------------------
\* Solution invariant (the model checker looks for its violation)
\* ----------------------------------------------------------------------
Solution == east # {}

=============================================================================