---- MODULE MissionariesAndCannibals
(***************************************************************************)
(* This module models the classic missionaries and cannibals problem.  A   *)
(* set of missionaries and a set of cannibals must all cross a river using  *)
(* a boat that can carry at most two people, and neither riverbank may ever  *)
(* hold more cannibals than missionaries (otherwise the missionaries are   *)
(* eaten).  The purpose of this spec is to model the problem so that the   *)
(* TLC model checker can discover a solution to it.                        *)
(*                                                                         *)
(* A step of the system moves a set of people across the river with the     *)
(* boat; that set is never empty and never larger than the boat's capacity. *)
(* The boat itself can never cross the river on its own.                   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(***************************************************************************)
(* bank_of_boat = which riverbank the boat is docked at.                    *)
(* who_is_on_bank[b] = the set of cannibals and missionaries on bank b.    *)
(***************************************************************************)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in {"E","W"} -> SUBSET (Missionaries \cup Cannibals)

Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E"
                                                THEN Missionaries \cup Cannibals
                                                ELSE {}]

(***************************************************************************)
(* A bank is safe if it holds no missionaries or the missionaries are not   *)
(* outnumbered by cannibals.                                               *)
(***************************************************************************)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(***************************************************************************)
(* A step moves a nonempty set S of at most two people from the boat's       *)
(* dock bank to the other bank, provided both banks are left in a safe      *)
(* state.  Primes denote the values of variables after the step; unprimed  *)
(* variables are the values before the step.                               *)
(***************************************************************************)
Move(S,b) == /\ Cardinality(S) \in {1,2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
                IN  /\ IsSafe(newThisBank)
                    /\ IsSafe(newOtherBank)
                    /\ bank_of_boat' = OtherBank(b)
                    /\ who_is_on_bank' = 
                         [i \in {"E","W"} |-> IF i = b THEN newThisBank
                                                ELSE newOtherBank]

Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(***************************************************************************)
(* An execution solves the problem when nobody remains on bank "E".  TLC     *)
(* reports an error trace whenever an invariant it is checking fails, so     *)
(* checking that bank "E" is never empty would *not* find a solution.  Instead *)
(* we check that bank "E" is never empty as an ordinary invariant, and let   *)
(* TLC's error trace be the solution itself.                                 *)
(***************************************************************************)
ProblemSolved == who_is_on_bank["E"] /= {}

====