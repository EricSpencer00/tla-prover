---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* ------------------------------------------------------------------- *)
(* Type correctness predicate                                            *)
(* ------------------------------------------------------------------- *)
TypeOK ==
    /\ bank_of_boat \in {"E", "W"}
    /\ who_is_on_bank \in [ {"E", "W"} -> SUBSET (Missionaries \cup Cannibals) ]

(* ------------------------------------------------------------------- *)
(* Initial state: everyone on the east bank, boat on east bank           *)
(* ------------------------------------------------------------------- *)
Init ==
    /\ bank_of_boat = "E"
    /\ who_is_on_bank = [ i \in {"E", "W"} |-> IF i = "E"
                                           THEN Missionaries \cup Cannibals
                                           ELSE {} ]

(* ------------------------------------------------------------------- *)
(* Safety condition for a single bank                                    *)
(* ------------------------------------------------------------------- *)
IsSafe(S) ==
    \/ S \subseteq Cannibals
    \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(* ------------------------------------------------------------------- *)
(* Helper to get the opposite bank                                        *)
(* ------------------------------------------------------------------- *)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* ------------------------------------------------------------------- *)
(* A move of a non‑empty set S (size 1 or 2) from bank b to the other bank*)
(* ------------------------------------------------------------------- *)
Move(S, b) ==
    /\ Cardinality(S) \in {1, 2}
    /\ LET newThisBank  == who_is_on_bank[b] \ S
           newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
       IN /\ IsSafe(newThisBank)
          /\ IsSafe(newOtherBank)
          /\ bank_of_boat' = OtherBank(b)
          /\ who_is_on_bank' = [ i \in {"E", "W"} |-> IF i = b
                                                     THEN newThisBank
                                                     ELSE newOtherBank ]

(* ------------------------------------------------------------------- *)
(* Next‑state relation: there exists an allowed move from the current bank*)
(* ------------------------------------------------------------------- *)
Next ==
    \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* ------------------------------------------------------------------- *)
(* Specification                                                            *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

(* ------------------------------------------------------------------- *)
(* Property used to find a solution (not an invariant)                  *)
(* ------------------------------------------------------------------- *)
Solution == who_is_on_bank["E"] = {}

=============================================================================