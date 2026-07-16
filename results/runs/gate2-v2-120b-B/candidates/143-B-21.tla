---- MODULE MissionariesAndCannibals
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* Type correctness predicate *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(* Initial state: everything starts on the east bank *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries ELSE {}]

(* Safety condition for a set of people on a bank *)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(* The opposite bank *)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* A safe move of a set S of people from bank b to the other bank *)
Move(S, b) == /\ Cardinality(S) \in {1, 2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
                IN  /\ IsSafe(newThisBank)
                    /\ IsSafe(newOtherBank)
                    /\ bank_of_boat' = OtherBank(b)
                    /\ who_is_on_bank' = 
                         [i \in {"E","W"} |-> 
                            IF i = b THEN newThisBank ELSE newOtherBank]

(* Next-state relation: any safe move of a non‑empty subset of the people on the current bank *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* Safety invariant: the east bank is never empty (its violation yields a solution trace) *)
Solution == who_is_on_bank["E"] /= {}

=============================================================================