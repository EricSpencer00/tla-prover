---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatAt, east, west

(* ----------------------------------------------------------------------
   Type invariant and safety condition for each bank
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ boatAt \in {"East","West"}
    /\ east \subseteq Missionaries \cup Cannibals
    /\ west \subseteq Missionaries \cup Cannibals
    /\ east \cap west = {}
    /\ east \cup west = Missionaries \cup Cannibals
    /\ Safe(east)
    /\ Safe(west)

Safe(bank) ==
    LET m == bank \cap Missionaries
        c == bank \cap Cannibals
    IN  \/ m = {}
        \/ Cardinality(c) <= Cardinality(m)

(* ----------------------------------------------------------------------
   Initial state: everyone on the east bank, boat docked at east
   ---------------------------------------------------------------------- *)
Init ==
    /\ boatAt = "East"
    /\ east = Missionaries \cup Cannibals
    /\ west = {}

(* ----------------------------------------------------------------------
   One crossing of the boat (one or two persons, never empty)
   ---------------------------------------------------------------------- *)
Move ==
    LET fromBank == IF boatAt = "East" THEN east ELSE west
        toBank   == IF boatAt = "East" THEN west ELSE east
        persons  == SUBSET fromBank
    IN /\ persons # {}                \* at least one person
       /\ Cardinality(persons) <= 2   \* at most two persons
       /\ boatAt' = IF boatAt = "East" THEN "West" ELSE "East"
       /\ IF boatAt = "East"
             THEN /\ east' = east \ persons
                  /\ west' = west \cup persons
             ELSE /\ west' = west \ persons
                  /\ east' = east \cup persons
       /\ Safe(east')
       /\ Safe(west')

Next == \/ Move

(* ----------------------------------------------------------------------
   Goal condition: all persons have reached the west bank
   ---------------------------------------------------------------------- *)
Solution == east = {}

====