---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   State variables
   ---------------------------------------------------------------------- *)
VARIABLES BoatPos, PeopleOnBank

(* ----------------------------------------------------------------------
   Derived sets
   ---------------------------------------------------------------------- *)
Banks == {"East", "West"}

People == Missionaries \cup Cannibals

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
    /\ BoatPos = "East"
    /\ PeopleOnBank = [b \in Banks |-> IF b = "East" THEN People ELSE {}]

(* ----------------------------------------------------------------------
   Safety / type predicate
   ---------------------------------------------------------------------- *)
SafeBank(b) ==
    LET M == {p \in PeopleOnBank[b] : p \in Missionaries}
        C == {p \in PeopleOnBank[b] : p \in Cannibals}
    IN  (M = {} ) \/ (Cardinality(C) <= Cardinality(M))

TypeOK ==
    /\ BoatPos \in Banks
    /\ PeopleOnBank \in [Banks -> SUBSET People]
    /\ \A b \in Banks : SafeBank(b)

(* ----------------------------------------------------------------------
   Boat moves (exactly 1 or 2 people)
   ---------------------------------------------------------------------- *)
Move ==
    \E grp \subseteq PeopleOnBank[BoatPos] :
        /\ Cardinality(grp) \in 1..2
        /\ LET dest == IF BoatPos = "East" THEN "West" ELSE "East" IN
           /\ PeopleOnBank' = [PeopleOnBank EXCEPT ![BoatPos] = PeopleOnBank[BoatPos] \ grp,
                                                    ![dest]      = PeopleOnBank[dest] \cup grp]
           /\ BoatPos' = dest
           /\ SafeBank(BoatPos)        \* safety of source bank after departure
           /\ SafeBank(dest)           \* safety of destination bank after arrival
        /\ UNCHANGED << >>

Next == Move

(* ----------------------------------------------------------------------
   Solution (goal) invariant – east bank becomes empty
   ---------------------------------------------------------------------- *)
Solution ==
    PeopleOnBank["East"] = {}

=============================================================================