---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

TypeOK ==
  /\ bank_of_boat \in {"E", "W"}
  /\ who_is_on_bank \in [{"E", "W"} -> SUBSET (Missionaries \cup Cannibals)]

Init ==
  /\ bank_of_boat = "E"
  /\ who_is_on_bank = [i \in {"E", "W"} |-> IF i = "E" THEN Missionaries \cup Cannibals ELSE {}]

Move(S, b) ==
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN /\ IsSafe(newThisBank)
        /\ IsSafe(newOtherBank)
        /\ bank_of_boat' = OtherBank(b)
        /\ who_is_on_bank' = [i \in {"E", "W"} |-> IF i = b THEN newThisBank ELSE newOtherBank]

Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

Solution == who_is_on_bank["E"] = {}

vars == <<bank_of_boat, who_is_on_bank>>
Spec == Init /\ [][Next]_vars
====