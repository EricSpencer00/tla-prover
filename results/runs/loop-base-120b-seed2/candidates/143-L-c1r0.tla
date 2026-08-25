---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

VARIABLES boatAt, BankPeople

(* ------------------------------------------------------------------- *)
(* Constants and derived sets                                            *)
(* ------------------------------------------------------------------- *)

Banks == {"East", "West"}

People == Missionaries \cup Cannibals

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                   *)
(* ------------------------------------------------------------------- *)

MissionariesOn(b) == { p \in Missionaries : p \in BankPeople[b] }

CannibalsOn(b)   == { p \in Cannibals   : p \in BankPeople[b] }

Safe(b) == 
    \/ MissionariesOn(b) = {} 
    \/ Cardinality(CannibalsOn(b)) <= Cardinality(MissionariesOn(b))

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

(* ------------------------------------------------------------------- *)
(* Type correctness predicate                                            *)
(* ------------------------------------------------------------------- *)

TypeOK == 
    /\ boatAt \in Banks
    /\ BankPeople \in [Banks -> SUBSET People]
    /\ \A p \in People : 
          \E! b \in Banks : p \in BankPeople[b]

(* ------------------------------------------------------------------- *)
(* Initial state                                                         *)
(* ------------------------------------------------------------------- *)

Init == 
    /\ boatAt = "East"
    /\ BankPeople = [b \in Banks |-> IF b = "East" THEN People ELSE {}]

(* ------------------------------------------------------------------- *)
(* Move action                                                          *)
(* ------------------------------------------------------------------- *)

Move == 
    \E grp \subseteq BankPeople[boatAt] : 
        /\ Cardinality(grp) \in 1..2
        /\ LET newBank == 
               [b \in Banks |-> 
                    IF b = boatAt          THEN BankPeople[b] \ grp
                    ELSE IF b = Opposite(boatAt) THEN BankPeople[b] \cup grp
                    ELSE BankPeople[b]]
           IN 
               /\ boatAt' = Opposite(boatAt)
               /\ BankPeople' = newBank
               /\ Safe("East")
               /\ Safe("West")

Next == Move

(* ------------------------------------------------------------------- *)
(* Solution invariant (violated when puzzle solved)                     *)
(* ------------------------------------------------------------------- *)

Solution == BankPeople["East"] # {}

====