---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatPos, location

(* the set of all persons *)
Person == Missionaries \cup Cannibals

(* banks identifiers *)
Banks == {"East", "West"}

(* safety predicate for a given distribution of persons *)
Safe(loc) ==
  \A b \in Banks :
    LET M == loc[b] \cap Missionaries ;
        C == loc[b] \cap Cannibals
    IN (M = {}) \/ (Cardinality(C) <= Cardinality(M))

(* type correctness invariant *)
TypeOK ==
  /\ boatPos \in Banks
  /\ location \in [Banks -> SUBSET Person]

(* initial state *)
Init ==
  /\ boatPos = "East"
  /\ location = [b \in Banks |-> IF b = "East" THEN Person ELSE {}]
  /\ TypeOK

(* next-state relation: move one or two persons across the river *)
Next ==
  \E grp \in SUBSET location[boatPos] :
    /\ Cardinality(grp) \in 1..2
    /\ LET other == IF boatPos = "East" THEN "West" ELSE "East" ;
           newLoc == [b \in Banks |->
                      IF b = boatPos THEN location[b] \ grp
                      ELSE IF b = other THEN location[b] \cup grp
                      ELSE location[b]]
       IN /\ Safe(newLoc)
          /\ boatPos' = other
          /\ location' = newLoc

(* solution condition: the east bank is empty *)
Solution == location["East"] = {}

====