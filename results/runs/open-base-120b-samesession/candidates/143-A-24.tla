---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANT Missionaries, Cannibals

VARIABLES boat, east, west

(* ----------------------------------------------------------------------
   Helper definitions
   ---------------------------------------------------------------------- *)

BankSide == {"East", "West"}

Safe(bank) ==
  LET m == Cardinality(bank \cap Missionaries) IN
  LET c == Cardinality(bank \cap Cannibals) IN
    (m = 0) \/ (c <= m)

(* ----------------------------------------------------------------------
   Type correctness and safety invariant
   ---------------------------------------------------------------------- *)

TypeOK ==
  /\ boat \in BankSide
  /\ east \subseteq Missionaries \cup Cannibals
  /\ west \subseteq Missionaries \cup Cannibals
  /\ east \cup west = Missionaries \cup Cannibals
  /\ east \cap west = {}
  /\ Safe(east)
  /\ Safe(west)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
  /\ boat = "East"
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

(* ----------------------------------------------------------------------
   Next-state relation (one crossing of the boat)
   ---------------------------------------------------------------------- *)

Next ==
  \/ /\ boat = "East"
     /\ \E grp \in SUBSET east :
          /\ Cardinality(grp) \in {1,2}
          /\ LET newEast == east \ grp,
                 newWest == west \cup grp
             IN /\ Safe(newEast) /\ Safe(newWest)
                /\ east'   = newEast
                /\ west'   = newWest
                /\ boat'   = "West"
  \/ /\ boat = "West"
     /\ \E grp \in SUBSET west :
          /\ Cardinality(grp) \in {1,2}
          /\ LET newWest == west \ grp,
                 newEast == east \cup grp
             IN /\ Safe(newWest) /\ Safe(newEast)
                /\ east'   = newEast
                /\ west'   = newWest
                /\ boat'   = "East"

(* ----------------------------------------------------------------------
   Solution condition (east bank empty)
   ---------------------------------------------------------------------- *)

Solution == east = {}

=============================================================================