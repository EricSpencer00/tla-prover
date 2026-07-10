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
(* Declaration of the sets of missionaries and cannibals.                  *)
(***************************************************************************)
CONSTANTS Missionaries, Cannibals 

(***************************************************************************)
(* Variables describing the current state.                                 *)
(***************************************************************************)
VARIABLES bank_of_boat, who_is_on_bank 

(***************************************************************************)
(* Type invariant for the variables.                                       *)
(***************************************************************************)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in 
                [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(***************************************************************************)
(* Initial state: everybody starts on the east bank and the boat is there. *)
(***************************************************************************)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                    ELSE {}]

(***************************************************************************)
(* Safety predicate for a bank.                                            *)
(***************************************************************************)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(***************************************************************************)
(* The opposite bank.                                                      *)
(***************************************************************************)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(***************************************************************************)
(* A move of a non‑empty set S (size 1 or 2) from bank b to the other bank. *)
(* The people in S are removed from b and added to the opposite bank.      *)
(* The resulting configuration must keep both banks safe.                  *)
(***************************************************************************)
Move(S, b) ==
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN  /\ IsSafe(newThisBank)
         /\ IsSafe(newOtherBank)
         /\ bank_of_boat' = OtherBank(b)
         /\ who_is_on_bank' =
              [i \in {"E","W"} |-> IF i = b THEN newThisBank
                                          ELSE newOtherBank]

(***************************************************************************)
(* Next‑state relation: any safe move of a non‑empty subset of the people   *)
(* currently on the bank where the boat is.                                 *)
(***************************************************************************)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : 
          Move(S, bank_of_boat)

(***************************************************************************)
(* The invariant used by TLC to discover a solution: there must always be  *)
(* someone left on the east bank.  When TLC finds a counter‑example, the   *)
(* final state will have who_is_on_bank["E"] = {} – a solution to the      *)
(* problem.                                                                 *)
(***************************************************************************)
Solution == who_is_on_bank["E"] /= {}

=============================================================================