---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------- *)
(* State variables                                                    *)
(* ------------------------------------------------------------------- *)

VARIABLES boat, east, west

vars == <<boat, east, west>>

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                 *)
(* ------------------------------------------------------------------- *)

Bank == {"East", "West"}

Safe(bankSet) ==
  \/ Missionaries \cap bankSet = {}
  \/ Cardinality(Cannibals \cap bankSet) <= Cardinality(Missionaries \cap bankSet)

(* ------------------------------------------------------------------- *)
(* Initialization                                                     *)
(* ------------------------------------------------------------------- *)

Init ==
  /\ boat = "East"
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

(* ------------------------------------------------------------------- *)
(* Type invariant                                                     *)
(* ------------------------------------------------------------------- *)

TypeOK ==
  /\ boat \in Bank
  /\ east \subseteq Missionaries \cup Cannibals
  /\ west \subseteq Missionaries \cup Cannibals
  /\ east \cup west = Missionaries \cup Cannibals
  /\ east \cap west = {}

(* ------------------------------------------------------------------- *)
(* Next-state relation                                                *)
(* ------------------------------------------------------------------- *)

Next ==
  \/ /\ boat = "East"
     /\ \E p \subseteq east :
          /\ Cardinality(p) \in 1..2
          /\ boat' = "West"
          /\ east' = east \ p
          /\ west' = west \cup p
          /\ Safe(east')
          /\ Safe(west')
  \/ /\ boat = "West"
     /\ \E p \subseteq west :
          /\ Cardinality(p) \in 1..2
          /\ boat' = "East"
          /\ west' = west \ p
          /\ east' = east \cup p
          /\ Safe(east')
          /\ Safe(west')

(* ------------------------------------------------------------------- *)
(* Solution invariant (used to detect a solved state)                *)
(* ------------------------------------------------------------------- *)

Solution == east # {}

=============================================================================