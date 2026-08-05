---- MODULE MissionariesAndCannibals ----
(***************************************************************************)
(* This module specifies a system that models the one described in the     *)
(* missionaries and cannibals problem.  See the Wikipedia article at       *)
(* https://en.wikipedia.org/wiki/Missionaries_and_cannibals_problem.       *)
(*                                                                         *)
(* The system's execution is a sequence of reachable states, where a state *)
(* is an assignment of values to the variables.  A step is a permissible *)
(* transition from one reachable state to its successor.                    *)
(*                                                                         *)
(* In this spec a step moves a set of up to two people from the boat's      *)
(* current bank to the other bank, so the state includes the bank the boat  *)
(* is on and, for each bank, the set of people on that bank.                *)
(*                                                                         *)
(* The purpose of this spec is to find a solution to the problem: a state *)
(* in which all the missionaries and cannibals have crossed to bank "W".    *)
(* Since a state with everyone on bank "W" violates the invariant         *)
(* who_is_on_bank["E"] /= {}, a TLC run checking that invariant will, when *)
(* it finds it violated, output a trace that ends in a solved state.       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Missionaries \cup Cannibals)]

Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |->
                                IF i = "E" THEN Missionaries \cup Cannibals ELSE {}]

\* It is safe for a bank to hold a set S of people iff either S has no     *
(* missionaries or cannibals do not outnumber the missionaries.           *)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* A step moving a set S of people from bank b to the other bank is safe if *
(* the resulting occupancy of both banks is safe and S is a non-empty set   *
(* of at most two people.                                                   *)
Move(S,b) == /\ Cardinality(S) \in {1,2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \ S
                IN /\ IsSafe(newThisBank) /\ IsSafe(newOtherBank)
                   /\ bank_of_boat' = OtherBank(b)
                   /\ who_is_on_bank' = [i \in {"E","W"} |->
                                            IF i = b THEN newThisBank ELSE newOtherBank]

Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

\* Every reachable state has someone left on bank "E": a TLC run checking
(* this invariance will produce a trace that ends in a state where nobody *)
(* is left on "E" -- a solution to the problem.                           *)
Solution == who_is_on_bank["E"] /= {}

====