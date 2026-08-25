---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES boatAt, east, west

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Bank == {"East", "West"}

CurrentBank(b) == IF b = "East" THEN east ELSE west
OppositeBank(b) == IF b = "East" THEN west ELSE east

Safe(bankSet) ==
  \/ Missionaries \cap bankSet = {}
  \/ Cardinality(Cannibals \cap bankSet) <= Cardinality(Missionaries \cap bankSet)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ boatAt \in Bank
  /\ east \subseteq Missionaries \cup Cannibals
  /\ west \subseteq Missionaries \cup Cannibals
  /\ east \cap west = {}
  /\ east \cup west = Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ boatAt = "East"
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

\* ----------------------------------------------------------------------
\* Next-state relation (one crossing of the boat)
\* ----------------------------------------------------------------------
Next ==
  \E g \in SUBSET (CurrentBank(boatAt)) :
    /\ Cardinality(g) \in 1..2
    /\ boatAt' = IF boatAt = "East" THEN "West" ELSE "East"
    /\ east' = IF boatAt = "East" THEN east \ g ELSE east \cup g
    /\ west' = IF boatAt = "East" THEN west \cup g ELSE west \ g
    /\ Safe(east')
    /\ Safe(west')

\* ----------------------------------------------------------------------
\* Solution predicate (all people have reached the west bank)
\* ----------------------------------------------------------------------
Solution == east = {}

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
\* ----------------------------------------------------------------------
\* (TLC will check both TypeOK and Solution)
\* ----------------------------------------------------------------------
====