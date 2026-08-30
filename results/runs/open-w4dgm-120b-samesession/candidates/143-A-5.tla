---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \union Cannibals
BoatCap == 2

VARIABLES boatAt, occupants

vars == <<boatAt, occupants>>

TypeOK ==
  /\ boatAt \in Banks
  /\ occupants \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ occupants = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move(s, g) ==
  /\ Cardinality(s) >= 1 /\ Cardinality(s) <= BoatCap
  /\ s \subseteq occupants[boatAt]
  /\ LET newOcc == [occupants EXCEPT ![boatAt] = @ \ s, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \union s]
     IN /\ \A b \in Banks :
          /\ (Missionaries \cap newOcc[b] = {}
             \/ Cardinality(Cannibals \cap newOcc[b]) <= Cardinality(Missionaries \cap newOcc[b]))
        /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
        /\ occupants' = newOcc

Next ==
  \E s \in SUBSET People : \E g \in Banks : Move(s, g)

Solution ==
  /\ Cardinality(occupants["west"]) = Cardinality(People)
  /\ occupants["east"] = {}

TypeOKInv == TypeOK

====