---- MODULE MissionariesAndCannibals ----
(***************************************************************************)
(* This module specifies a system that models the one described in the     *)
(* missionaries and cannibals problem.  This is a classic problem in which  *)
(* three missionaries and three cannibals must cross a river using a boat   *)
(* that can carry at most two people, under the constraint that, on either  *)
(* bank, if there are missionaries present they cannot be outnumbered by    *)
(* cannibals (if they were, the cannibals would eat them).  The boat cannot *)
(* cross the river by itself.  The TLC model checker can find a solution   *)
(* to the problem by model-checking this spec, where a solution is an       *)
(* execution that ends with everyone on the far bank.                       *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(***************************************************************************)
(* bank_of_boat is the bank of the river on which the boat is docked.       *)
(* who_is_on_bank[b] is the set of missionaries and cannibals on bank b --  *)
(* an array indexed by the two banks {"E","W"}.                             *)
(***************************************************************************)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(***************************************************************************)
(* The initial state: everyone starts on the east bank.                     *)
(***************************************************************************)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E" THEN Cannibals \cup Missionaries ELSE {}]

(***************************************************************************)
(* It is safe for a set S of people to be on a bank when either no          *)
(* missionaries are there, or the cannibals do not outnumber the            *)
(* missionaries.                                                             *)
(***************************************************************************)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(***************************************************************************)
(* A step that moves a set S of people from bank b to the other bank is     *)
(* safe iff the resulting populations on both banks are safe.  Moving is   *)
(* subject to the boat's capacity of at most two people.                    *)
(***************************************************************************)
Move(S, b) == /\ Cardinality(S) \in {1, 2}
              /\ LET newThisBank  == who_is_on_bank[b] \ S
                     newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
                 IN /\ IsSafe(newThisBank)
                    /\ IsSafe(newOtherBank)
                    /\ bank_of_boat' = OtherBank(b)
                    /\ who_is_on_bank' = [i \in {"E","W"} |-> IF i = b THEN newThisBank ELSE newOtherBank]

(***************************************************************************)
(* The boat can make a step whenever there is a nonempty subset of the     *)
(* people on the bank it is on that can be moved safely.                    *)
(***************************************************************************)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

vars == <<bank_of_boat, who_is_on_bank>>

(***************************************************************************)
(* The TLC model checker is used here to prove (or find a counterexample   *)
(* to) that every reachable state still has someone left on the east bank  *)
(* before the boat reaches the far side.  When TLC finds this is not an    *)
(* invariant it prints a trace ending in a state with no one on the east    *)
(* bank -- which is exactly a solution to the problem.                     *)
(***************************************************************************)
Solution == who_is_on_bank["E"] /= {}

Spec == Init /\ [][Next]_vars

====