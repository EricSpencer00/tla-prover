---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------- *)
(* Derived sets *)
MissionarySet == Missionaries
CannibalSet   == Cannibals
People        == MissionarySet \cup CannibalSet

(* ------------------------------------------------------------------- *)
(* State variables *)
VARIABLES boat, east, west

(* ------------------------------------------------------------------- *)
(* Type invariant (used as a sanity check) *)
TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

(* ------------------------------------------------------------------- *)
(* Helper definitions *)

(* Number of missionaries on a given bank *)
MissionariesOn(b) == Cardinality(b \cap MissionarySet)

(* Number of cannibals on a given bank *)
CannibalsOn(b) == Cardinality(b \cap CannibalSet)

(* Safety condition for a bank: either no missionaries, or missionaries >= cannibals *)
SafeBank(b) == (MissionariesOn(b) = 0) \/ (MissionariesOn(b) >= CannibalsOn(b))

(* Safety condition for the whole state *)
Safe == /\ SafeBank(east)
        /\ SafeBank(west)

(* ------------------------------------------------------------------- *)
(* One crossing move *)

Move ==
    /\ boat = "East"
    /\ \E g \in {1,2} :
        \E group \subseteq east :
            /\ Cardinality(group) = g
            /\ \A p \in group : p \in People
            /\ LET newEast == east \ group
               IN /\ SafeBank(newEast)
                  /\ SafeBank(west \cup group)
            /\ boat' = "West"
            /\ east' = east \ group
            /\ west' = west \cup group

\* Symmetric move from West to East
Move ==
    /\ boat = "East"
    /\ \E g \in {1,2} :
        \E group \subseteq east :
            /\ Cardinality(group) = g
            /\ LET newEast == east \ group
               IN /\ SafeBank(newEast)
                  /\ SafeBank(west \cup group)
            /\ boat' = "West"
            /\ east' = east \ group
            /\ west' = west \cup group

Move ==
    /\ boat = "West"
    /\ \E g \in {1,2} :
        \E group \subseteq west :
            /\ Cardinality(group) = g
            /\ LET newWest == west \ group
               IN /\ SafeBank(newWest)
                  /\ SafeBank(east \cup group)
            /\ boat' = "East"
            /\ west' = west \ group
            /\ east' = east \cup group

(* ------------------------------------------------------------------- *)
(* Next-state relation *)
Next == Move

(* ------------------------------------------------------------------- *)
(* Safety invariant required by the .cfg file *)
Solution == east = {}

====