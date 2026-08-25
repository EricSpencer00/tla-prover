---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

VARIABLES boat, east, west

(*--- Type invariant ---------------------------------------------------*)
TypeOK ==
  /\ boat \in {"East", "West"}
  /\ east \subseteq Missionaries \cup Cannibals
  /\ west \subseteq Missionaries \cup Cannibals
  /\ east \cap west = {}
  /\ east \cup west = Missionaries \cup Cannibals

(*--- Safety of a single bank -------------------------------------------*)
SafeBank(b) ==
  LET m == Cardinality(b \cap Missionaries)
      c == Cardinality(b \cap Cannibals)
  IN (m = 0) \/ (c <= m)

Safe ==
  /\ SafeBank(east)
  /\ SafeBank(west)

(*--- Initial state -----------------------------------------------------*)
Init ==
  /\ boat = "East"
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

(*--- One move of the boat ---------------------------------------------*)
Move ==
  \/ /\ boat = "East"
        /\ \E grp \subseteq east :
               /\ Cardinality(grp) \in {1, 2}
               /\ LET newEast == east \ grp
                      newWest == west \cup grp
                  IN /\ SafeBank(newEast) /\ SafeBank(newWest)
                     /\ boat'  = "West"
                     /\ east'  = newEast
                     /\ west'  = newWest
  \/ /\ boat = "West"
        /\ \E grp \subseteq west :
               /\ Cardinality(grp) \in {1, 2}
               /\ LET newWest == west \ grp
                      newEast == east \cup grp
                  IN /\ SafeBank(newWest) /\ SafeBank(newEast)
                     /\ boat'  = "East"
                     /\ east'  = newEast
                     /\ west'  = newWest

Next == Move

(*--- Goal condition (solution) ----------------------------------------*)
Solution == east = {}

====