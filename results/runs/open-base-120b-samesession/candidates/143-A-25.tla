---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* All people involved in the puzzle *)
People == Missionaries \cup Cannibals

VARIABLES boat, east

(* ----------------------------------------------------------------------
   Type correctness
   ---------------------------------------------------------------------- *)
TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq People

(* ----------------------------------------------------------------------
   Safety condition for a single bank
   ---------------------------------------------------------------------- *)
SafeBank(b) ==
    LET m == Cardinality(b \cap Missionaries) ;
        c == Cardinality(b \cap Cannibals)
    IN (m = 0) \/ (c <= m)

Safety ==
    /\ SafeBank(east)
    /\ SafeBank(People \ east)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ boat = "East"
    /\ east = People

(* ----------------------------------------------------------------------
   One crossing of the boat
   ---------------------------------------------------------------------- *)
Move ==
    \E grp \in SUBSET(People) :
        /\ Cardinality(grp) \in {1, 2}
        /\ grp \subseteq (IF boat = "East" THEN east ELSE People \ east)
        /\ LET newEast == 
                IF boat = "East" THEN east \ grp ELSE east \cup grp
           IN
               /\ SafeBank(newEast)
               /\ SafeBank(People \ newEast)
               /\ boat' = (IF boat = "East" THEN "West" ELSE "East")
               /\ east' = newEast

Next == Move

(* ----------------------------------------------------------------------
   Invariant that the puzzle has not yet been solved (east bank non‑empty)
   ---------------------------------------------------------------------- *)
Solution == east # {}

====