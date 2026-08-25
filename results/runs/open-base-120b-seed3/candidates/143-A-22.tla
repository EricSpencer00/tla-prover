---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
Person == Missionaries \cup Cannibals
Banks   == {"East", "West"}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES BoatPos, Bank

\* ----------------------------------------------------------------------
\* Safety predicate for a single bank given a set of people on it
\* ----------------------------------------------------------------------
SafeBank(bset) ==
  LET m == Cardinality(bset \cap Missionaries) ,
      c == Cardinality(bset \cap Cannibals)
  IN  (m = 0) \/ (c <= m)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ BoatPos = "East"
  /\ Bank = [b \in Banks |-> IF b = "East" THEN Person ELSE {}]

\* ----------------------------------------------------------------------
\* Move action: transport 1 or 2 people across the river
\* ----------------------------------------------------------------------
Move ==
  \E passengers \in SUBSET (Bank[BoatPos]) :
    /\ Cardinality(passengers) \in 1..2
    LET other   == IF BoatPos = "East" THEN "West" ELSE "East"
        newBank == [b \in Banks |-> 
                     IF b = BoatPos THEN Bank[BoatPos] \ passengers
                     ELSE IF b = other THEN Bank[other] \cup passengers
                     ELSE {}]
    IN /\ SafeBank(newBank[BoatPos])
       /\ SafeBank(newBank[other])
       /\ BoatPos' = other
       /\ Bank'    = newBank

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == Move

\* ----------------------------------------------------------------------
\* Type-correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ BoatPos \in Banks
  /\ Bank \in [Banks -> SUBSET Person]
  /\ Missionaries \cap Cannibals = {}
  /\ Cardinality(Missionaries) = 3
  /\ Cardinality(Cannibals)   = 3
  /\ Person = Missionaries \cup Cannibals

\* ----------------------------------------------------------------------
\* Solution predicate (goal reached when east bank is empty)
\* ----------------------------------------------------------------------
Solution == Bank["East"] = {}

====