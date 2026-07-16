---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

\* ----------------------------------------------------------------------
\* Type invariant (kept unchanged)
\* ----------------------------------------------------------------------
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

\* ----------------------------------------------------------------------
\* Initial state (kept unchanged)
\* ----------------------------------------------------------------------
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE {}]

\* ----------------------------------------------------------------------
\* Safety condition for a bank
\* ----------------------------------------------------------------------
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

\* ----------------------------------------------------------------------
\* Helper to get the opposite bank
\* ----------------------------------------------------------------------
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* ----------------------------------------------------------------------
\* Move action – corrected to add people to the destination bank
\* ----------------------------------------------------------------------
Move(S, b) ==
  /\ Cardinality(S) \in {1,2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN /\ IsSafe(newThisBank)
        /\ IsSafe(newOtherBank)
        /\ bank_of_boat' = OtherBank(b)
        /\ who_is_on_bank' =
            [i \in {"E","W"} |-> IF i = b THEN newThisBank
                                         ELSE newOtherBank]

\* ----------------------------------------------------------------------
\* Next-state relation (kept unchanged except for using the corrected Move)
\* ----------------------------------------------------------------------
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

\* ----------------------------------------------------------------------
\* Invariant used by the model to find a solution
\* ----------------------------------------------------------------------
Solution == who_is_on_bank["E"] /= {}

=============================================================================