---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------- *)
(* Derived sets *)
People == Missionaries \cup Cannibals
Banks  == {"East", "West"}
BoatSides == Banks

(* Partition of people into missionaries and cannibals for convenience *)
IsMissionary == { p \in People : p \in Missionaries }
IsCannibal   == { p \in People : p \in Cannibals }

(* ------------------------------------------------------------------- *)
(* Variables *)
VARIABLES boat, east

(* ------------------------------------------------------------------- *)
(* Helper definitions *)

EastSet == east
WestSet == People \ east

BoatAtEast == (boat = "East")
BoatAtWest == (boat = "West")

MissionaryCountOnEast == Cardinality(EastSet \cap Missionaries)
CannibalCountOnEast   == Cardinality(EastSet \cap Cannibals)

MissionaryCountOnWest == Cardinality(WestSet \cap Missionaries)
CannibalCountOnWest   == Cardinality(WestSet \cap Cannibals)

(* Safety condition for a single bank *)
SafeBank(b) ==
    LET ms == { p \in b : p \in Missionaries } IN
    LET cs == { p \in b : p \in Cannibals } IN
    (Cardinality(ms) = 0) \/ (Cardinality(cs) <= Cardinality(ms))

SafeEast == SafeBank(EastSet)
SafeWest == SafeBank(WestSet)

(* Safety of the whole state *)
StateSafe == SafeEast /\ SafeWest

(* ------------------------------------------------------------------- *)
(* Initial state *)

Init ==
    /\ boat = "East"
    /\ east = People
    /\ StateSafe

(* ------------------------------------------------------------------- *)
(* Move action *)

Move ==
    /\ boat = "East"
    /\ \E grp \in SUBSET(EastSet) :
        /\ Cardinality(grp) \in 1..2
        /\ east' = east \ grp
        /\ boat' = "West"
        /\ StateSafe

\/
    /\ boat = "West"
    /\ \E grp \in SUBSET(WestSet) :
        /\ Cardinality(grp) \in 1..2
        /\ east' = east \cup grp
        /\ boat' = "East"
        /\ StateSafe

Next == Move

(* ------------------------------------------------------------------- *)
(* Specification (for completeness, though not directly referenced) *)
Spec == Init /\ [][Next]_<<boat, east>>

(* ------------------------------------------------------------------- *)
(* Type correctness invariant (ensures variables stay within domains) *)

TypeOK ==
    /\ boat \in BoatSides
    /\ east \subseteq People
    /\ StateSafe

(* ------------------------------------------------------------------- *)
(* Solution invariant: the east bank is never empty (the model checker
   will look for a violation of this invariant to find a solution). *)

Solution == east # {}

=============================================================================