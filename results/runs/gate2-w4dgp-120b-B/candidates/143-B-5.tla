---- MODULE MissionariesAndCannibals ----
(***************************************************************************)
(* This module specifies a system that models the one described in the     *)
(* missionaries and cannibals problem.  On 20 December 2018, Wikipedia       *)
(* contained the following description of this problem:                    *)
(*                                                                         *)
(*    [T]hree missionaries and three cannibals must cross a river using    *)
(*    a boat which can carry at most two people, under the constraint      *)
(*    that, for both banks, if there are missionaries present on the       *)
(*    bank, they cannot be outnumbered by cannibals (if they were, the     *)
(*    cannibals would eat the missionaries).  The boat cannot cross the    *)
(*    river by itself with no people on board.                             *)
(*                                                                         *)
(* As explained below, we can use this specification and the TLC model     *)
(* checker to find a solution to the problem.                              *)
(***************************************************************************)

(* The following EXTENDS statement imports definitions of the ordinary     *)
(* arithmetic operations on integers and the definition of the Cardinality *)
(* operator, where Cardinality(S) is the number of elements in S if S is a *)
(* finite set.                                                             *)
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals 

(* In a TLA+ spec, an execution is a sequence of states, where a state is  *)
(* an assignment of values to the spec's variables.  A step is a pair of    *)
(* successive states.  We write s -> t to indicate that s, t is a step.    *)
(*                                                                         *)
(* This model breaks each crossing into a single step moving a set of       *)
(* people with the boat from one bank to the other.                        *)
(*                                                                         *)
(* bank_of_boat: the bank the boat is docked at.                            *)
(* who_is_on_bank: for each bank b, the set of people on bank b.           *)
(*                                                                         *)
(* Although not needed to specify the system, we define a state predicate  *)
(* TypeOK that tells the reader (and TLC) the types of the variables.      *)
(*                                                                         *)
(* The next-state relation is defined by two formulas: Init (the set of    *)
(* initial states) and Next (the set of allowed steps).                     *)
(*                                                                         *)
(* The purpose of this spec is to find a solution to the missionaries and  *)
(* cannibals problem: an execution in which everyone reaches the other      *)
(* bank.  To find it, run TLC and have it check that who_is_on_bank["E"]  *)
(* is never empty; TLC will then report a counterexample, which is the      *)
(* solution.                                                                *)

TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE {} ]

(* It is safe for a bank to be in state S iff either there are no          *)
(* missionaries in S, or the cannibals do not outnumber the missionaries.   *)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* A step that moves a set S of people from b to the other bank is allowed  *)
(* iff S is one or two people, the resulting bank populations are safe, the *)
(* boat is moved across, and the moved people switch banks.                 *)
Move(S,b) == /\ Cardinality(S) \in {1,2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \cap S
                IN  /\ IsSafe(newThisBank) 
                    /\ IsSafe(newOtherBank)
                    /\ bank_of_boat' = OtherBank(b)
                    /\ who_is_on_bank' = 
                         [i \in {"E","W"} |-> IF i = b THEN newThisBank 
                                                       ELSE newOtherBank]    

Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* TLC will report an execution that falsifies this (a solution) by       *)
(* showing a state with an empty east bank.                                *)
Solution == who_is_on_bank["E"] /= {}

====