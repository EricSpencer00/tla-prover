---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in 
                [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

\* ----------------------------------------------------------------------
\* Initial state – everyone starts on the east bank
\* ----------------------------------------------------------------------
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE {}]

\* ----------------------------------------------------------------------
\* Safety condition for a single bank
\* ----------------------------------------------------------------------
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

\* ----------------------------------------------------------------------
\* Helper to get the opposite bank
\* ----------------------------------------------------------------------
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* ----------------------------------------------------------------------
\* A move of a non‑empty set S (size 1 or 2) from bank b to the opposite
\* bank.  The unprimed variables refer to the source state, primed to the
\* destination state.
\* ----------------------------------------------------------------------
Move(S, b) == 
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN /\ IsSafe(newThisBank)
        /\ IsSafe(newOtherBank)
        /\ bank_of_boat' = OtherBank(b)
        /\ who_is_on_bank' = [i \in {"E","W"} |-> 
                                 IF i = b THEN newThisBank 
                                 ELSE newOtherBank]

\* ----------------------------------------------------------------------
\* Next‑state relation: any safe move of a non‑empty subset of the people
\* on the bank where the boat currently is.
\* ----------------------------------------------------------------------
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] \ 
            /\ S # {} 
            : Move(S, bank_of_boat)

\* ----------------------------------------------------------------------
\* The safety invariant required by the original description
\* ----------------------------------------------------------------------
Solution == who_is_on_bank["E"] # {}

=============================================================================