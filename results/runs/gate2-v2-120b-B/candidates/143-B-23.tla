---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* ------------------------------------------------------------------------- *)
(* Type correctness predicate                                                  *)
(* ------------------------------------------------------------------------- *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Missionaries \cup Cannibals)]

(* ------------------------------------------------------------------------- *)
(* Initial state                                                              *)
(* ------------------------------------------------------------------------- *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E"
                                                THEN Missionaries \cup Cannibals
                                                ELSE {}]

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                         *)
(* ------------------------------------------------------------------------- *)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

IsSafe(S) == \/ S \subseteq Missionaries
            \/ Cardinality(S \cap Missionaries) >= Cardinality(S \cap Cannibals)

(* ------------------------------------------------------------------------- *)
(* A move of a set S of people from bank b to the opposite bank                *)
(* ------------------------------------------------------------------------- *)
Move(S, b) ==
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN /\ IsSafe(newThisBank)
        /\ IsSafe(newOtherBank)
        /\ bank_of_boat' = OtherBank(b)
        /\ who_is_on_bank' = [i \in {"E","W"} |-> IF i = b THEN newThisBank ELSE newOtherBank]

(* ------------------------------------------------------------------------- *)
(* Next-state relation                                                        *)
(* ------------------------------------------------------------------------- *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* ------------------------------------------------------------------------- *)
(* Specification                                                              *)
(* ------------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

(* ------------------------------------------------------------------------- *)
(* Desired property (used by the model checker to find a solution)            *)
(* ------------------------------------------------------------------------- *)
Solution == who_is_on_bank["E"] /= {}

=============================================================================