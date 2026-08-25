---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals
Banks   == {"East", "West"}

(* ----------------------------------------------------------------------
   Variables
   ---------------------------------------------------------------------- *)
VARIABLES boatPos, east, west

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ boatPos \in Banks
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

(* ----------------------------------------------------------------------
   Safety condition for a single bank
   ---------------------------------------------------------------------- *)
Safe(bank) ==
    LET m == Cardinality(bank \cap Missionaries) ;
        c == Cardinality(bank \cap Cannibals)
    IN  (m = 0) \/ (c <= m)

SafeState ==
    /\ Safe(east)
    /\ Safe(west)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ boatPos = "East"
    /\ east = People
    /\ west = {}
    /\ TypeOK

(* ----------------------------------------------------------------------
   Move action
   ---------------------------------------------------------------------- *)
Move ==
    \E grp \subseteq People :
        /\ grp # {}
        /\ Cardinality(grp) \in 1 .. 2
        /\ IF boatPos = "East"
              THEN grp \subseteq east
              ELSE grp \subseteq west
        LET newEast ==
                IF boatPos = "East"
                    THEN east \ grp
                    ELSE east \cup grp
            newWest ==
                IF boatPos = "West"
                    THEN west \ grp
                    ELSE west \cup grp
            newPos  == IF boatPos = "East" THEN "West" ELSE "East"
        IN  /\ boatPos' = newPos
            /\ east'    = newEast
            /\ west'    = newWest
            /\ SafeState

Next == Move

(* ----------------------------------------------------------------------
   Solution condition (invariant)
   ---------------------------------------------------------------------- *)
Solution == east = {}

====