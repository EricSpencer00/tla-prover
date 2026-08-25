---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(*-------------------------------------------------------------------*)
(* Derived constants                                                  *)
(*-------------------------------------------------------------------*)
Persons == Missionaries \cup Cannibals
Bank    == {"East", "West"}

(*-------------------------------------------------------------------*)
(* Assumptions about the constants                                    *)
(*-------------------------------------------------------------------*)
ASSUME /\ Missionaries # {}
       /\ Cannibals   # {}
       /\ Missionaries \cap Cannibals = {}
       /\ Cardinality(Missionaries) = 3
       /\ Cardinality(Cannibals)   = 3

(*-------------------------------------------------------------------*)
(* State variables                                                    *)
(*-------------------------------------------------------------------*)
VARIABLES boatAt, loc

(*-------------------------------------------------------------------*)
(* Type correctness invariant                                         *)
(*-------------------------------------------------------------------*)
TypeOK ==
    /\ boatAt \in Bank
    /\ loc \in [Persons -> Bank]

(*-------------------------------------------------------------------*)
(* Safety of a single bank (parameterized by a location function)    *)
(*-------------------------------------------------------------------*)
BankSafe(locs, b) ==
    LET M == { p \in Missionaries : locs[p] = b }
        C == { p \in Cannibals   : locs[p] = b }
    IN  ( Cardinality(M) = 0 ) \/ ( Cardinality(C) <= Cardinality(M) )

(*-------------------------------------------------------------------*)
(* Initial state                                                     *)
(*-------------------------------------------------------------------*)
Init ==
    /\ boatAt = "East"
    /\ \A p \in Persons : loc[p] = "East"
    /\ /\ BankSafe(loc, "East")
       /\ BankSafe(loc, "West")

(*-------------------------------------------------------------------*)
(* Helper: opposite bank                                              *)
(*-------------------------------------------------------------------*)
Opposite(b) == IF b = "East" THEN "West" ELSE "East"

(*-------------------------------------------------------------------*)
(* Move action: transport 1 or 2 people across the river            *)
(*-------------------------------------------------------------------*)
Move ==
    \E grp \subseteq Persons :
        /\ Cardinality(grp) \in 1..2
        /\ \A p \in grp : loc[p] = boatAt          \* all board from current bank
        /\ boatAt' = Opposite(boatAt)
        /\ loc' = [p \in Persons |-> 
                     IF p \in grp THEN Opposite(boatAt) ELSE loc[p]]
        /\ BankSafe(loc', "East")
        /\ BankSafe(loc', "West")
        /\ UNCHANGED << >>

Next == Move

(*-------------------------------------------------------------------*)
(* Solution condition: everyone has reached the west bank            *)
(*-------------------------------------------------------------------*)
Solution == \A p \in Persons : loc[p] = "West"

====