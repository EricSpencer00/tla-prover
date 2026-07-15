---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------- *)
(* Derived sets *)
People == Missionaries \cup Cannibals
Banks  == {"East", "West"}

(* ------------------------------------------------------------------- *)
(* State variables *)
VARIABLES boat, east, west

(* ------------------------------------------------------------------- *)
(* Helper definitions *)
BoatAtEast == boat = "East"
BoatAtWest == boat = "West"

EastBank == east
WestBank == west

(* The set of people currently on the same bank as the boat *)
PeopleOnBoatBank == IF BoatAtEast THEN EastBank ELSE WestBank

(* The set of people on the opposite bank *)
PeopleOnOtherBank == IF BoatAtEast THEN WestBank ELSE EastBank

(* ------------------------------------------------------------------- *)
(* Safety predicate for a single bank *)
SafeBank(s) ==
    LET m == Cardinality(s \cap Missionaries) IN
    LET c == Cardinality(s \cap Cannibals) IN
    (m = 0) \/ (c <= m)

(* ------------------------------------------------------------------- *)
(* Type correctness invariant (helps TLC) *)
TypeOK ==
    /\ boat \in Banks
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

(* ------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

(* ------------------------------------------------------------------- *)
(* Move action: choose 1 or 2 people from the current bank, move them *)
Move ==
    \E movers \in SUBSET PeopleOnBoatBank :
        /\ Cardinality(movers) \in {1, 2}
        /\ LET newEast ==
                IF BoatAtEast
                    THEN east \ movers
                    ELSE east \cup movers
           IN
           LET newWest ==
                IF BoatAtWest
                    THEN west \ movers
                    ELSE west \cup movers
           IN
           /\ SafeBank(newEast)
           /\ SafeBank(newWest)
           /\ boat' = IF boat = "East" THEN "West" ELSE "East"
           /\ east' = newEast
           /\ west' = newWest

Next == Move

(* ------------------------------------------------------------------- *)
(* Safety invariant required by the description *)
Solution == east = {}

(* ------------------------------------------------------------------- *)
(* Specification *)
Spec == Init /\ [][Next]_<<boat, east, west>>

=============================================================================