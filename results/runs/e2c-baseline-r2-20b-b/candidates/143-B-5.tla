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

(***************************************************************************)
(* The following EXTENDS statement imports definitions of the ordinary     *)
(* arithmetic operations on integers and the definition of the Cardinality *)
(* operator, where Cardinality(S) is the number of elements in S if S is a *)
(* finite set.                                                             *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

(***************************************************************************)
(* Next comes the declaration of the sets of missionaries and cannibals.   *)
(***************************************************************************)
CONSTANTS Missionaries, Cannibals 

(***************************************************************************)
(* In TLA+, an execution of a system is described as a sequence of states, *)
(* where a state is an assignment of values to variables.  A pair of successive *)
(* states in an execution is called a step.  We write s -> t to indicate that s, t is a step in an execution. *)
(*                                                                         *)
(* The first thing to do when writing a system specification is to decide what *)
(* should constitute a step.  In this specification, a step consists of moving a set of people with the boat from one bank to the other. *)
(*                                                                         *)
(* A state of the system must describe on which bank the boat is and what people are on each bank. *)
(* We describe this with two variables: *)
(*                                                                         *)
(*    bank_of_boat: the bank where the boat is docked ("E" or "W").      *)
(*    who_is_on_bank: a function mapping each bank to the set of people on that bank. *)
(*                                                                         *)
(* Instead of declaring a constant Banks, we simply use the constants "E" and "W". *)
(***************************************************************************)
VARIABLES bank_of_boat, who_is_on_bank 

(***************************************************************************)
(* TypeOK describes the expected types of the variables in any reachable state. *)
(***************************************************************************)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in 
                [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(***************************************************************************)
(* The initial-state formula Init asserts that the boat and all the cannibals and missionaries are on the east bank. *)
(***************************************************************************)                             
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE  {} ]

(***************************************************************************)
(* Operators used in defining the next-state formula Next. *)
(***************************************************************************)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(***************************************************************************)
(* Move(S,b) describes a safe move of the set S of people from bank b to the other bank. *)
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

(***************************************************************************)
(* Next describes all safe moves from the current bank_of_boat. *)
(***************************************************************************)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : 
            Move(S, bank_of_boat)

(***************************************************************************)
(* Solution property: an invariant that is violated when the missionaries *)
(* and cannibals all reach the west bank. *)
(***************************************************************************)                  
Solution == who_is_on_bank["E"] /= {}

=============================================================================