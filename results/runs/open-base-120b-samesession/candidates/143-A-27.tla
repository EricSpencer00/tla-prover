---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals
CONSTANTS East, West

VARIABLES boat, east, west

(*--- Safety of a single bank -----------------------------------*)
Safe(b) ==
  LET m == Cardinality(b \cap Missionaries)
      c == Cardinality(b \cap Cannibals)
  IN (m = 0) \/ (c <= m)

(*--- Type correctness ------------------------------------------*)
TypeOK ==
  /\ boat \in {East, West}
  /\ east \subseteq Missionaries \cup Cannibals
  /\ west \subseteq Missionaries \cup Cannibals
  /\ east \cap west = {}
  /\ east \cup west = Missionaries \cup Cannibals
  /\ Missionaries \cap Cannibals = {}
  /\ Safe(east)
  /\ Safe(west)

(*--- Initial state --------------------------------------------*)
Init ==
  /\ boat = East
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

(*--- One crossing of the boat ---------------------------------*)
Move ==
  LET curBank   == IF boat = East THEN east ELSE west
      otherBank == IF boat = East THEN west ELSE east
      grp \in SUBSET curBank
  IN
    /\ grp # {}
    /\ Cardinality(grp) \in {1, 2}
    /\ boat' = IF boat = East THEN West ELSE East
    /\ IF boat = East THEN
         /\ east' = curBank \ grp
         /\ west' = otherBank \cup grp
       ELSE
         /\ east' = otherBank \cup grp
         /\ west' = curBank \ grp
    /\ Safe(east')
    /\ Safe(west')

Next == Move

(*--- Specification (optional) ---------------------------------*)
Spec == Init /\ [][Next]_<<boat, east, west>>

(*--- Invariant used to detect a solution ----------------------*)
Solution == east # {}

====