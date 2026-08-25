---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(*   Sets and derived constants                                            *)
(* ---------------------------------------------------------------------- *)

Bank == {"East", "West"}

AllPeople == Missionaries \cup Cannibals

(* ---------------------------------------------------------------------- *)
(*   Variables                                                            *)
(* ---------------------------------------------------------------------- *)

VARIABLES BoatAt, East   \* BoatAt \in Bank, East \subseteq AllPeople

(* ---------------------------------------------------------------------- *)
(*   Helper definitions                                                   *)
(* ---------------------------------------------------------------------- *)

West == AllPeople \ East

MissionariesOn(S) == S \cap Missionaries
CannibalsOn(S)    == S \cap Cannibals

Safe(S) == 
    \/ MissionariesOn(S) = {} 
    \/ Cardinality(CannibalsOn(S)) <= Cardinality(MissionariesOn(S))

CurrentBank == IF BoatAt = "East" THEN East ELSE West
OtherBank   == IF BoatAt = "East" THEN West ELSE East

(* ---------------------------------------------------------------------- *)
(*   Type correctness predicate                                            *)
(* ---------------------------------------------------------------------- *)

TypeOK == 
    /\ BoatAt \in Bank
    /\ East \subseteq AllPeople

(* ---------------------------------------------------------------------- *)
(*   Initial state                                                         *)
(* ---------------------------------------------------------------------- *)

Init == 
    /\ BoatAt = "East"
    /\ East = AllPeople

(* ---------------------------------------------------------------------- *)
(*   Move action                                                          *)
(* ---------------------------------------------------------------------- *)

Move == 
    \E passengers \in SUBSET CurrentBank :
        /\ Cardinality(passengers) \in 1..2
        /\ LET NewEast == 
                IF BoatAt = "East" 
                THEN East \ passengers 
                ELSE East \cup passengers
           IN 
              /\ Safe(NewEast)
              /\ Safe(AllPeople \ NewEast)
              /\ BoatAt' = IF BoatAt = "East" THEN "West" ELSE "East"
              /\ East' = NewEast

(* ---------------------------------------------------------------------- *)
(*   Next-state relation                                                   *)
(* ---------------------------------------------------------------------- *)

Next == 
    \/ Move
    \/ UNCHANGED <<BoatAt, East>>

(* ---------------------------------------------------------------------- *)
(*   Invariant stating the puzzle is not yet solved (used for counter-   *)
(*   example generation)                                                  *)
(* ---------------------------------------------------------------------- *)

Solution == East # {}

(* ---------------------------------------------------------------------- *)
(*   Specification                                                         *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<BoatAt, East>>

=============================================================================