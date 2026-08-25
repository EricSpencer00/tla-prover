---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, east, west

(* ------------------------------------------------------------------- *)
(* Helper definitions *)

Safe(bank) == 
    /\ (Cardinality(bank \cap Missionaries) = 0)
       \/ (Cardinality(bank \cap Cannibals) <= Cardinality(bank \cap Missionaries))

(* ------------------------------------------------------------------- *)
(* State predicates *)

Init ==
    /\ boat = "East"
    /\ east = Missionaries \cup Cannibals
    /\ west = {}

(* ------------------------------------------------------------------- *)
(* Action: Move a group of 1 or 2 people across the river *)

Move ==
    LET src == IF boat = "East" THEN east ELSE west
        dst == IF boat = "East" THEN west ELSE east
    IN
    \E people \in SUBSET(src) :
        /\ Cardinality(people) \in 1..2
        /\ boat' = IF boat = "East" THEN "West" ELSE "East"
        /\ IF boat = "East"
              THEN /\ east' = east \ persons
                   /\ west' = west \cup persons
              ELSE /\ east' = east \cup persons
                   /\ west' = west \ persons
        /\ Safe(east')
        /\ Safe(west')
    WHERE persons == people \* alias for readability

Next == Move

(* ------------------------------------------------------------------- *)
(* Invariants *)

TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq Missionaries \cup Cannibals
    /\ west \subseteq Missionaries \cup Cannibals
    /\ east \cap west = {}

Solution == east # {}

====