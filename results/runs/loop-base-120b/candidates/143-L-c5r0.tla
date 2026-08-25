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
People == Missionaries \cup Cannibals

Safe(bank) ==
  LET m == Cardinality({ x \in bank : x \in Missionaries })
      c == Cardinality({ x \in bank : x \in Cannibals })
  IN (m = 0) \/ (c <= m)

CurrentBankPeople ==
  IF boat = "East" THEN east ELSE west

OtherBankPeople ==
  IF boat = "East" THEN west ELSE east

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ boat \in {"East", "West"}
  /\ east \subseteq People
  /\ west \subseteq People
  /\ east \cap west = {}
  /\ east \cup west = People

\* ----------------------------------------------------------------------
\* Safety: each bank must be safe
\* ----------------------------------------------------------------------
BanksSafe == Safe(east) /\ Safe(west)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ boat = "East"
  /\ east = People
  /\ west = {}

\* ----------------------------------------------------------------------
\* Move action (boat carries 1 or 2 people, never empty)
\* ----------------------------------------------------------------------
Move ==
  \E S \subseteq CurrentBankPeople :
    /\ (Cardinality(S) = 1) \/ (Cardinality(S) = 2)
    /\ LET newEast ==
           IF boat = "East" THEN east \ S ELSE east \cup S
         newWest ==
           IF boat = "East" THEN west \cup S ELSE west \ S
       IN /\ newEast = IF boat = "East" THEN east \ S ELSE east \cup S
          /\ newWest = IF boat = "East" THEN west \cup S ELSE west \ S
          /\ Safe(newEast) /\ Safe(newWest)
          /\ boat' = IF boat = "East" THEN "West" ELSE "East"
          /\ east' = newEast
          /\ west' = newWest

Next == Move

\* ----------------------------------------------------------------------
\* Solution invariant: the east bank is required to stay non‑empty.
\* Its violation corresponds to a solved puzzle.
\* ----------------------------------------------------------------------
Solution == east /= {}

\* ----------------------------------------------------------------------
\* Specification (optional, not required by the .cfg but often useful)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boat, east, west>>

====