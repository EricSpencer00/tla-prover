---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatPos, east

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
People == Missionaries \cup Cannibals

WestBank == People \ east

BankSet(pos) == IF pos = "East" THEN east ELSE WestBank

\* ----------------------------------------------------------------------
\* Safety predicate for a single bank
\* ----------------------------------------------------------------------
Safe(bank) ==
  /\ Cardinality(bank \cap Missionaries) = 0
     \/ Cardinality(bank \cap Cannibals) <= Cardinality(bank \cap Missionaries)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ boatPos \in {"East", "West"}
  /\ east \subseteq People

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ boatPos = "East"
  /\ east = People

\* ----------------------------------------------------------------------
\* One crossing of the boat
\* ----------------------------------------------------------------------
Move ==
  \E G \subseteq BankSet(boatPos) :
    /\ Cardinality(G) \in 1..2
    /\ LET eastPrime ==
          IF boatPos = "East"
          THEN east \ G
          ELSE east \cup G
       IN
          /\ east' = eastPrime
          /\ boatPos' = IF boatPos = "East" THEN "West" ELSE "East"
          /\ Safe(eastPrime)
          /\ Safe(People \ eastPrime)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Move

\* ----------------------------------------------------------------------
\* Solution predicate (goal reached)
\* ----------------------------------------------------------------------
Solution == east = {}

\* ----------------------------------------------------------------------
\* Specification (optional, not required by the cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boatPos, east>>

====