---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* Basic assumptions about the constants *)
ASSUME /\ Missionaries # {}
       /\ Cannibals # {}
       /\ Missionaries ∩ Cannibals = {}
       /\ Cardinality(Missionaries) = 3
       /\ Cardinality(Cannibals) = 3

VARIABLES boat, east, west

(* The set of all persons *)
Person == Missionaries ∪ Cannibals

Banks == {"East", "West"}

(* Type correctness invariant *)
TypeOK ==
    /\ boat ∈ Banks
    /\ east ⊆ Person
    /\ west ⊆ Person
    /\ east ∩ west = {}
    /\ east ∪ west = Person

(* Safety of a single bank *)
Safe(bank) ==
    LET m == bank ∩ Missionaries
        c == bank ∩ Cannibals
    IN (m = {}) \/ (Cardinality(c) <= Cardinality(m))

(* Initial state *)
Init ==
    /\ boat = "East"
    /\ east = Person
    /\ west = {}

(* One crossing of the boat *)
Next ==
    ∃ moving \in SUBSET Person :
        /\ (boat = "East" => moving ⊆ east)
        /\ (boat = "West" => moving ⊆ west)
        /\ Cardinality(moving) \in 1..2
        /\ LET newBoat == IF boat = "East" THEN "West" ELSE "East"
               newEast == IF boat = "East" THEN east \ moving ELSE east ∪ moving
               newWest == IF boat = "East" THEN west ∪ moving ELSE west \ moving
           IN
               /\ boat' = newBoat
               /\ east' = newEast
               /\ west' = newWest
               /\ Safe(newEast)
               /\ Safe(newWest)

(* Invariant stating that the puzzle is solved when the east bank is empty *)
Solution == east = {}

====