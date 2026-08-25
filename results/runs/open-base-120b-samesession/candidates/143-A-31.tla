---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* Derived set of all people
People == Missionaries \cup Cannibals

\* The two river banks
BankSide == {"East", "West"}

\* Opposite bank function
Opposite(b) == IF b = "East" THEN "West" ELSE "East"

VARIABLES boatPos, bank

\*=====================================================================
\* Safety predicate for a given bank side
Safe(b) ==
  LET m == Cardinality( bank[b] \cap Missionaries )
      c == Cardinality( bank[b] \cap Cannibals )
  IN  (m = 0) \/ (c <= m)

\*=====================================================================
\* Initialization
Init ==
  /\ boatPos = "East"
  /\ bank = [b \in BankSide |-> IF b = "East" THEN People ELSE {}]

\*=====================================================================
\* One move of the boat (carrying 1 or 2 persons)
Move ==
  \E passengers \in SUBSET People :
    /\ Cardinality(passengers) \in 1..2
    /\ passengers \subseteq bank[boatPos]
    LET newPos == Opposite(boatPos) IN
      /\ boatPos' = newPos
      /\ bank' = [b \in BankSide |
                    IF b = boatPos
                       THEN bank[b] \ setminus passengers
                       ELSE IF b = newPos
                              THEN bank[b] \cup passengers
                              ELSE bank[b]]
      /\ Safe("East") /\ Safe("West")

Next == Move

\*=====================================================================
\* Type correctness invariant
TypeOK ==
  /\ boatPos \in BankSide
  /\ bank \in [BankSide -> SUBSET People]
  /\ (bank["East"] \cup bank["West"]) = People
  /\ (bank["East"] \cap bank["West"] = {})

\*=====================================================================
\* Solution invariant (the puzzle is solved when the east bank is empty)
Solution == bank["East"] = {}

====