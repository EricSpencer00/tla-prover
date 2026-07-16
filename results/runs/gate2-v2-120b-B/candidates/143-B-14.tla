---- MODULE MissionariesAndCannibals
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

\* Type invariant describing the shape of the state variables
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Missionaries \cup Cannibals)]

\* Initial state: everybody starts on the east bank, the boat is also on the east bank
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E"
                                           THEN Missionaries \cup Cannibals
                                           ELSE {}]

\* Safety condition for a set of people on a bank
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

\* Helper that gives the opposite bank
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* A move of a non‑empty set S (size 1 or 2) from bank b to the opposite bank
Move(S, b) ==
    /\ Cardinality(S) \in {1, 2}
    /\ LET newThisBank  == who_is_on_bank[b] \ S
           newOtherBank == (who_is_on_bank[OtherBank(b)] \cup S)
       IN /\ IsSafe(newThisBank)
          /\ IsSafe(newOtherBank)
          /\ bank_of_boat' = OtherBank(b)
          /\ who_is_on_bank' = [i \in {"E","W"} |-> IF i = b
                                                    THEN newThisBank
                                                    ELSE newOtherBank]

\* Next-state relation: pick any non‑empty subset of the people on the current bank
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : 
           Move(S, bank_of_boat)

\* Safety invariant: the people on each bank are always safe (kept for model checking)
SafetyInv == /\ IsSafe(who_is_on_bank["E"])
             /\ IsSafe(who_is_on_bank["W"])

\* Property used to extract a solution: eventually the east bank becomes empty
Solution == <> (who_is_on_bank["E"] = {})

\* Explicitly expose the actions for TLC's view
vars == <<bank_of_boat, who_is_on_bank>>

\* The overall specification
Spec == Init /\ [][Next]_vars

====