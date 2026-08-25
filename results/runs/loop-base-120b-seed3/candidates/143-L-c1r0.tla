---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES boatAt, east, west

(* ----------------------------------------------------------------------
   Derived definitions
   ---------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals

Banks == {"East", "West"}

(* The set of variables for the stuttering operator *)
vars == <<boatAt, east, west>>

(* ----------------------------------------------------------------------
   Helper predicates
   ---------------------------------------------------------------------- *)
Safe(bankSet) ==
    LET m == Cardinality(bankSet \cap Missionaries) IN
    LET c == Cardinality(bankSet \cap Cannibals) IN
    (m = 0) \/ (c <= m)

CurrentBank ==
    IF boatAt = "East" THEN east ELSE west

DestinationBank ==
    IF boatAt = "East" THEN west ELSE east

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ boatAt \in Banks
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cap west = {}
    /\ east \cup west = People

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ boatAt = "East"
    /\ east = People
    /\ west = {}

(* ----------------------------------------------------------------------
   Transition relation (one move of the boat)
   ---------------------------------------------------------------------- *)
Next ==
    \E g \in SUBSET CurrentBank :
        /\ Cardinality(g) \in 1..2
        /\ LET newEast ==
                IF boatAt = "East"
                THEN east \ g
                ELSE east \cup g
           IN LET newWest ==
                IF boatAt = "East"
                THEN west \cup g
                ELSE west \ g
           IN /\ boatAt' = IF boatAt = "East" THEN "West" ELSE "East"
              /\ east' = newEast
              /\ west' = newWest
              /\ Safe(newEast)
              /\ Safe(newWest)

(* ----------------------------------------------------------------------
   Solution condition (all people have reached the west bank)
   ---------------------------------------------------------------------- *)
Solution == east = {}

====