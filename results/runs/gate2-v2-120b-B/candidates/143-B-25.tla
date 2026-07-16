---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

\* Types of the variables
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Missionaries \cup Cannibals)]

\* Initial state: everyone on the east bank, boat on east bank
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E" THEN Missionaries \cup Cannibals ELSE {}]

\* Safety predicate for a set of people on a bank
IsSafe(S) == \/ S \subseteq Missionaries
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* Move a non‑empty set S (size 1 or 2) from bank b to the opposite bank
Move(S, b) ==
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN /\ IsSafe(newThisBank)
        /\ IsSafe(newOtherBank)
        /\ bank_of_boat' = OtherBank(b)
        /\ who_is_on_bank' = [i \in {"E","W"} |-> IF i = b THEN newThisBank ELSE newOtherBank]

\* Next‑state relation: choose any admissible S on the current boat bank
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

\* The specification (for TLC)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

\* Solution predicate: eventually everybody reaches the west bank
Solution == who_is_on_bank["E"] = {}

=============================================================================