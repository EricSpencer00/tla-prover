---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
  /\ bank_of_boat \in {"E", "W"}
  /\ who_is_on_bank \in [{"E", "W"} -> SUBSET (Missionaries \cup Cannibals)]

\* ----------------------------------------------------------------------
\* Initial state: everybody starts on the east bank
\* ----------------------------------------------------------------------
Init ==
  /\ bank_of_boat = "E"
  /\ who_is_on_bank = [i \in {"E", "W"} |-> IF i = "E"
                                          THEN Missionaries \cup Cannibals
                                          ELSE {}]

\* ----------------------------------------------------------------------
\* Safety condition for a set of people standing on a bank
\* ----------------------------------------------------------------------
IsSafe(S) ==
  \/ S \subseteq Missionaries          \* no cannibals present
  \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

\* ----------------------------------------------------------------------
\* The opposite bank
\* ----------------------------------------------------------------------
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* ----------------------------------------------------------------------
\* A move of a non‑empty set S of 1 or 2 people from bank b to the other bank
\* ----------------------------------------------------------------------
Move(S, b) ==
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN /\ IsSafe(newThisBank)
        /\ IsSafe(newOtherBank)
        /\ bank_of_boat' = OtherBank(b)
        /\ who_is_on_bank' = [i \in {"E", "W"} |-> IF i = b
                                                         THEN newThisBank
                                                         ELSE newOtherBank]

\* ----------------------------------------------------------------------
\* The next‑state relation: any safe move from the current boat bank
\* ----------------------------------------------------------------------
Next ==
  \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

\* ----------------------------------------------------------------------
\* Safety property (kept for completeness; the model checks a different
\* invariant to drive the search for a solution)
\* ----------------------------------------------------------------------
Solution == who_is_on_bank["E"] /= {}

=============================================================================