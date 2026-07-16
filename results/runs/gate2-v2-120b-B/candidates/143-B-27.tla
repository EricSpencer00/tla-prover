---- MODULE MissionariesAndCannibals
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* --------------------------------------------------------------- *)
(* Type correctness predicate                                       *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Missionaries \cup Cannibals)]

(* --------------------------------------------------------------- *)
(* Initial state: everyone on the east bank                         *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Missionaries \cup Cannibals
                               ELSE {}]

(* --------------------------------------------------------------- *)
(* Safety condition for a set of people on a bank                  *)
IsSafe(S) == \/ S \subseteq Missionaries
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(* --------------------------------------------------------------- *)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* --------------------------------------------------------------- *)
(* A move consists of transporting a non‑empty set of 1 or 2 people *)
(* from the boat’s current bank to the opposite bank, provided the *)
(* resulting populations on both banks are safe.                    *)
Move(S, b) == 
    /\ Cardinality(S) \in {1, 2}
    /\ S \subseteq who_is_on_bank[b]            \* people must be on the current bank
    /\ LET newThisBank  == who_is_on_bank[b] \ S
           newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
       IN /\ IsSafe(newThisBank)
          /\ IsSafe(newOtherBank)
          /\ bank_of_boat' = OtherBank(b)
          /\ who_is_on_bank' = [i \in {"E","W"} |-> 
                                  IF i = b THEN newThisBank 
                                  ELSE newOtherBank]

(* --------------------------------------------------------------- *)
(* Next permits any safe move of a non‑empty set of 1 or 2 people *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* --------------------------------------------------------------- *)
(* The spec permits all behaviors that start in Init and follow Next *)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

(* --------------------------------------------------------------- *)
(* Invariant used by TLC to find a solution: there is someone left *)
(* on the east bank until the final state where everybody is on the *)
(* west bank.                                                       *)
Solution == who_is_on_bank["E"] /= {}

====