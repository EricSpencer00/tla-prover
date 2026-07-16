---- MODULE MissionariesAndCannibals
(***************************************************************************)
(* This module specifies a system that models the one described in the     *)
(* missionaries and cannibals problem.                                      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* Type correctness invariant *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(* Initial state: everyone on the east bank, boat on the east bank *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E" THEN Cannibals \cup Missionaries ELSE {}]

(* Safety condition for a set of people on a bank *)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(* The opposite bank *)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* A move of a non‑empty set S (size 1 or 2) from bank b to the opposite bank *)
Move(S, b) == /\ Cardinality(S) \in {1, 2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
                IN  /\ IsSafe(newThisBank)
                    /\ IsSafe(newOtherBank)
                    /\ bank_of_boat' = OtherBank(b)
                    /\ who_is_on_bank' = [i \in {"E","W"} |-> IF i = b THEN newThisBank ELSE newOtherBank]

(* One of the possible safe moves, based on where the boat currently is *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* We want to find a solution, so we look for a state where no one remains on the east bank *)
Solution == who_is_on_bank["E"] = {}

=============================================================================