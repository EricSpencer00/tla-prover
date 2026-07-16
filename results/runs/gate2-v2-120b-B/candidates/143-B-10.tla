---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

\* ----------------------------------------------------------------------
\* Type correctness predicate (unchanged)
\* ----------------------------------------------------------------------
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in 
                [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

\* ----------------------------------------------------------------------
\* Initial state (unchanged)
\* ----------------------------------------------------------------------
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE  {} ]

\* ----------------------------------------------------------------------
\* Safety predicate for a bank (unchanged)
\* ----------------------------------------------------------------------
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

\* ----------------------------------------------------------------------
\* Helper to get the opposite bank (unchanged)
\* ----------------------------------------------------------------------
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* ----------------------------------------------------------------------
\* A move of a non‑empty set S of people from bank b to the other bank.
\* The original spec used the set difference operator "\" to remove S
\* from the destination bank, which was incorrect and caused a deadlock.
\* The corrected definition adds S to the destination bank using set union.
\* ----------------------------------------------------------------------
Move(S, b) == 
    /\ Cardinality(S) \in {1,2}
    /\ LET newThisBank  == who_is_on_bank[b] \ S
           newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
       IN  /\ IsSafe(newThisBank)
           /\ IsSafe(newOtherBank)
           /\ bank_of_boat' = OtherBank(b)
           /\ who_is_on_bank' = 
                [i \in {"E","W"} |-> IF i = b THEN newThisBank 
                                                ELSE newOtherBank]

\* ----------------------------------------------------------------------
\* Next-state relation: any safe move of a non‑empty subset of the people
\* on the current bank.
\* ----------------------------------------------------------------------
Next == \E S \in who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

\* ----------------------------------------------------------------------
\* The specification: initial condition and next-state relation, together
\* with the type correctness predicate.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>> /\ TypeOK

\* ----------------------------------------------------------------------
\* Solution predicate used as an invariant in the original description.
\* ----------------------------------------------------------------------
Solution == who_is_on_bank["E"] /= {}

=============================================================================