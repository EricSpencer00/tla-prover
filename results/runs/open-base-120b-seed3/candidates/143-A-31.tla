---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(*  Derived sets                                                          *)
(* ---------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals

(* ---------------------------------------------------------------------- *)
(*  Variables                                                             *)
(* ---------------------------------------------------------------------- *)

VARIABLES BoatPos, east, west

(* ---------------------------------------------------------------------- *)
(*  Helper definitions                                                    *)
(* ---------------------------------------------------------------------- *)

Safe(bank) == 
    (bank \cap Missionaries = {}) 
    \/ (Cardinality(bank \cap Cannibals) <= Cardinality(bank \cap Missionaries))

TypeOK == 
    /\ BoatPos \in {"East", "West"}
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cap west = {}
    /\ east \cup west = People

(* ---------------------------------------------------------------------- *)
(*  Initial state                                                         *)
(* ---------------------------------------------------------------------- *)

Init == 
    /\ BoatPos = "East"
    /\ east = People
    /\ west = {}

(* ---------------------------------------------------------------------- *)
(*  Move action (one or two people cross)                                 *)
(* ---------------------------------------------------------------------- *)

Move ==
    \/ /\ BoatPos = "East"
       /\ \E grp \subseteq east:
            /\ Cardinality(grp) \in 1..2
            /\ LET newEast == east \ grp
                   newWest == west \cup grp
               IN
                  /\ Safe(newEast)
                  /\ Safe(newWest)
                  /\ BoatPos' = "West"
                  /\ east' = newEast
                  /\ west' = newWest
    \/ /\ BoatPos = "West"
       /\ \E grp \subseteq west:
            /\ Cardinality(grp) \in 1..2
            /\ LET newWest == west \ grp
                   newEast == east \cup grp
               IN
                  /\ Safe(newWest)
                  /\ Safe(newEast)
                  /\ BoatPos' = "East"
                  /\ east' = newEast
                  /\ west' = newWest

Next == Move

(* ---------------------------------------------------------------------- *)
(*  Invariants                                                            *)
(* ---------------------------------------------------------------------- *)

Solution == east # {}

=============================================================================