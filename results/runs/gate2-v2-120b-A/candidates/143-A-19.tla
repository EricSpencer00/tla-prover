---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

(* --constants that will be instantiated in the .cfg file-- *)
CONSTANTS Missionaries, Cannibals

(* derived constant *)
People == Missionaries \cup Cannibals

(* the two banks *)
Banks == {"East", "West"}

VARIABLES boat, east, west

(* Helper definitions *)
BoatAtEast == boat = "East"
BoatAtWest == boat = "West"

BankSet(b) == IF b = "East" THEN east ELSE west

(* The type-correctness invariant required by the cfg *)
TypeOK == 
    /\ boat \in Banks
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

(* Safety condition for a single bank *)
SafeBank(b) ==
    LET m == Cardinality({ p \in b : p \in Missionaries })
        c == Cardinality({ p \in b : p \in Cannibals })
    IN  (m = 0) \/ (c <= m)

(* The overall safety invariant required by the cfg *)
Solution == SafeBank(east) /\ SafeBank(west)

(* Initial state described in the natural-language text *)
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

(* One or two distinct people to travel together *)
PeopleCombo == { S \in SUBSET People : Cardinality(S) \in 1..2 }

(* An individual crossing action *)
Cross ==
    \/ /\ BoatAtEast
       /\ \E S \in PeopleCombo :
            /\ S \subseteq east
            /\ west' = west \cup S
            /\ east' = east \ S
            /\ boat' = "West"
            /\ SafeBank(east')
            /\ SafeBank(west')
    \/ /\ BoatAtWest
       /\ \E S \in PeopleCombo :
            /\ S \subseteq west
            /\ east' = east \cup S
            /\ west' = west \ S
            /\ boat' = "East"
            /\ SafeBank(east')
            /\ SafeBank(west')

Next == Cross

(* Specification entry point, not used directly by the cfg but useful for completeness *)
Spec == Init /\ [][Next]_<<boat, east, west>>

====