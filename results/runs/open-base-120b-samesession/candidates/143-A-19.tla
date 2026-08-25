---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

VARIABLES Boat, East

(* The set of all people *)
People == Missionaries \cup Cannibals

(* ----------------------------------------------------------------------
   Type correctness invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ Boat \in {"East", "West"}
    /\ East \subseteq People

(* ----------------------------------------------------------------------
   Initial state: everyone is on the east bank and the boat is docked there
   ---------------------------------------------------------------------- *)
Init ==
    /\ Boat = "East"
    /\ East = People

(* ----------------------------------------------------------------------
   Safety predicate for a bank
   ---------------------------------------------------------------------- *)
Safe(bank) ==
    LET m == Cardinality(bank \cap Missionaries) IN
    LET c == Cardinality(bank \cap Cannibals) IN
    \/ m = 0
       \/ c <= m

(* ----------------------------------------------------------------------
   One crossing of the boat (the only possible transition)
   ---------------------------------------------------------------------- *)
Move ==
    LET CurrentBank == IF Boat = "East" THEN East ELSE People \ East IN
    \E g \in SUBSET CurrentBank :
        /\ (Cardinality(g) = 1) \/ (Cardinality(g) = 2)
        /\ LET newEast ==
                IF Boat = "East"
                THEN East \ g
                ELSE East \/ g
           IN
            /\ Safe(newEast)
            /\ Safe(People \ newEast)
            /\ Boat' = IF Boat = "East" THEN "West" ELSE "East"
            /\ East' = newEast

Next == Move

(* ----------------------------------------------------------------------
   Invariant used to detect a solution: the east bank must stay non‑empty.
   When the invariant is violated, all people have reached the west bank.
   ---------------------------------------------------------------------- *)
Solution == East # {}

====