---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* The set of all people *)
Persons == Missionaries \cup Cannibals

VARIABLES boat, east

(* People on the west bank – derived from east *)
West == Persons \ east

(* ------------------------------------------------------------------- *)
(* Type invariant *)
TypeOK ==
    /\ boat \in {"East","West"}
    /\ east \subseteq Persons

(* ------------------------------------------------------------------- *)
(* Safety condition for a bank *)
Safe(bank) ==
    LET m == {p \in bank : p \in Missionaries}
        c == {p \in bank : p \in Cannibals}
    IN ( (Cardinality(m) = 0) \/ (Cardinality(c) <= Cardinality(m)) )

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ boat = "East"
    /\ east = Persons

(* ------------------------------------------------------------------- *)
(* One crossing of the boat *)
Next ==
    \E grp \in SUBSET Persons :
        /\ Cardinality(grp) \in 1..2
        /\ ( IF boat = "East"
              THEN grp \subseteq east
              ELSE grp \subseteq West )
        /\ LET newEast == IF boat = "East"
                           THEN east \ grp
                           ELSE east \cup grp
           IN /\ Safe(newEast)
              /\ Safe(Persons \ newEast)
              /\ boat' = ( IF boat = "East" THEN "West" ELSE "East" )
              /\ east' = newEast

(* ------------------------------------------------------------------- *)
(* Solution reached when the east bank is empty *)
Solution == east = {}

====