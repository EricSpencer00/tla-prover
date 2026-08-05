---- MODULE MissionariesAndCannibals
(***************************************************************************)
(* This module specifies a system that models the one described in the     *)
(* missionaries and cannibals problem.  On 20 December 2018, Wikipedia     *)
(* contained the following description of this problem.                    *)
(*                                                                         *)
(*    [T]hree missionaries and three cannibals must cross a river using    *)
(*    a boat which can carry at most two people, under the constraint      *)
(*    that, for both banks, if there are missionaries present on the       *)
(*    bank, they cannot be outnumbered by cannibals (if they were, the     *)
(*    cannibals would eat the missionaries).  The boat cannot cross the    *)
(*    river by itself with no people on board.                             *)
(*                                                                         *)
(* As explained below, we can use the specification and the TLC model      *)
(* checker to find a solution to the problem.                              *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(***************************************************************************)
(* bank_of_boat is the riverbank on which the boat is docked, and            *)
(* who_is_on_bank[b] is the set of people on riverbank b.                   *)
(***************************************************************************)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E" THEN Cannibals \cup Missionaries ELSE {}]

(***************************************************************************)
(* The set of people on a bank is safe iff either there are no missionaries *)
(* on it or the missionaries are not outnumbered by cannibals.               *)
(***************************************************************************)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(***************************************************************************)
(* Move(S,b) describes a safe move of a set S of people from bank b to the  *)
(* other bank: what must hold in the state before the move (unprimed       *)
(* variables) and how the two variables are updated by the move (primed    *)
(* variables).                                                              *)
(***************************************************************************)
Move(S,b) == /\ Cardinality(S) \in {1,2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \cap S
                IN /\ IsSafe(newThisBank)
                   /\ IsSafe(newOtherBank)
                   /\ bank_of_boat' = OtherBank(b)
                   /\ who_is_on_bank' = [i \in {"E","W"} |-> IF i = b THEN newThisBank ELSE newOtherBank]

(***************************************************************************)
(* A step moves some set of people from the bank where the boat is docked   *)
(* to the other bank.                                                       *)
(***************************************************************************)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(***************************************************************************)
(* The point of the spec is to solve the problem: an execution in which    *)
(* everyone reaches bank "W".  TLC finds such an execution by checking     *)
(* that an invariant expressing that someone is left on bank "E" is not     *)
(* reachable.                                                               *)
(***************************************************************************)
Solution == who_is_on_bank["E"] /= {}

====