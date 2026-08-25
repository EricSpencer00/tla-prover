---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

\* --------------------------------------------------------------
\* Basic assumptions about the constants (optional but helpful)
ASSUME /\ Missionaries # {}
       /\ Cannibals # {}
       /\ Missionaries \cap Cannibals = {}
       /\ Cardinality(Missionaries) = 3
       /\ Cardinality(Cannibals) = 3

VARIABLES boat, east, west

\* --------------------------------------------------------------
\* Helper definitions
East  == "East"
West  == "West"
Banks == {East, West}

IsEast(b) == b = East
OtherBank(b) == IF b = East THEN West ELSE East

\* Safety predicate for a single bank
Safe(b) ==
  LET m == Cardinality(b \cap Missionaries)
      c == Cardinality(b \cap Cannibals)
  IN  (m = 0) \/ (c <= m)

\* --------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
  /\ boat \in Banks
  /\ east  \subseteq (Missionaries \cup Cannibals)
  /\ west  \subseteq (Missionaries \cup Cannibals)
  /\ east \cap west = {}
  /\ east \cup west = Missionaries \cup Cannibals

\* --------------------------------------------------------------
\* Solution invariant – the model checker looks for a violation
Solution == east # {}

\* --------------------------------------------------------------
\* Initial state
Init ==
  /\ boat = East
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

\* --------------------------------------------------------------
\* One move of the boat
Move ==
  \E passengers \in SUBSET (IF boat = East THEN east ELSE west) :
    /\ Cardinality(passengers) \in 1..2
    /\ LET newEast ==
           IF boat = East THEN east \ passengers ELSE east \cup passengers
         newWest ==
           IF boat = East THEN west \cup passengers ELSE west \ passengers
       IN /\ Safe(newEast) /\ Safe(newWest)
    /\ boat' = OtherBank(boat)
    /\ east' = newEast
    /\ west' = newWest

\* --------------------------------------------------------------
Next == Move

\* --------------------------------------------------------------
\* Specification (optional, not required by the .cfg but useful)
Spec == Init /\ [][Next]_<<boat, east, west>>

====