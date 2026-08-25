---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, east, west

(* ---------------------------------------------------------------------- *)
(* Helper definitions *)

AllPeople == Missionaries \cup Cannibals

CountMissionaries(b) == Cardinality({ p \in b : p \in Missionaries })
CountCannibals(b)    == Cardinality({ p \in b : p \in Cannibals })

Safe(b) == 
    \/ CountMissionaries(b) = 0
    \/ CountCannibals(b) <= CountMissionaries(b)

(* ---------------------------------------------------------------------- *)
(* Type correctness *)

TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq AllPeople
    /\ west \subseteq AllPeople
    /\ east \cap west = {}
    /\ east \cup west = AllPeople

(* ---------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ boat = "East"
    /\ east = AllPeople
    /\ west = {}

(* ---------------------------------------------------------------------- *)
(* Move action *)

Move ==
    LET curBank   == IF boat = "East" THEN east ELSE west
        otherBank == IF boat = "East" THEN west ELSE east
    IN
    \E people \in SUBSET curBank :
        /\ (Cardinality(people) = 1) \/ (Cardinality(people) = 2)
        /\ LET newEast == IF boat = "East" THEN east \ people ELSE east \cup people
               newWest == IF boat = "East" THEN west \cup people ELSE west \ people
               newBoat == IF boat = "East" THEN "West" ELSE "East"
           IN
              /\ newBoat \in {"East", "West"}
              /\ newEast \subseteq AllPeople
              /\ newWest \subseteq AllPeople
              /\ newEast \cap newWest = {}
              /\ Safe(newEast) /\ Safe(newWest)
              /\ boat' = newBoat
              /\ east' = newEast
              /\ west' = newWest

Next == Move

(* ---------------------------------------------------------------------- *)
(* Solution invariant: violation yields a solution trace *)

Solution == east # {}

====