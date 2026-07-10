---- MODULE MissionariesAndCannibals ----------------------
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
(* Variables describing the current state.                                 *)
(***************************************************************************)
VARIABLES bank_of_boat, who_is_on_bank 

(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in 
                [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(***************************************************************************)
(* Initial state: everyone starts on the east bank.                         *)
(***************************************************************************)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE {}]

(***************************************************************************)
(* Safety condition for a bank.                                            *)
(***************************************************************************)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(***************************************************************************)
(* The opposite bank.                                                      *)
(***************************************************************************)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(***************************************************************************)
(* A move of a non‑empty set S (size 1 or 2) from bank b to the other bank. *)
(* The move is allowed only if the resulting distribution of people on both *)
(* banks is safe.                                                            *)
(***************************************************************************)
Move(S, b) == 
    /\ Cardinality(S) \in {1, 2}
    /\ S \subseteq who_is_on_bank[b]               \* S must be taken from the current bank
    /\ LET newThisBank  == who_is_on_bank[b] \ S
           newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
       IN  /\ IsSafe(newThisBank)
           /\ IsSafe(newOtherBank)
           /\ bank_of_boat' = OtherBank(b)
           /\ who_is_on_bank' = 
                [i \in {"E","W"} |-> IF i = b THEN newThisBank 
                                          ELSE newOtherBank]

(***************************************************************************)
(* Next-state relation: there exists a legal move from the bank where the *)
(* boat currently is.                                                       *)
(***************************************************************************)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : 
            Move(S, bank_of_boat)

(***************************************************************************)
(* Invariant used to obtain a solution: eventually the east bank becomes   *)
(* empty.  TLC finds a counterexample to this invariant, which is a        *)
(* successful crossing.                                                     *)
(***************************************************************************)
Solution == who_is_on_bank["E"] /= {}

=============================================================================