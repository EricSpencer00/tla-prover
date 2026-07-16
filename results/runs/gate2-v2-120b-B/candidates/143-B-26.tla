---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* --algorithm MissionariesAndCannibals
variables bank_of_boat = "E";
variables who_is_on_bank = [i \in {"E","W"} |-> IF i = "E"
                                            THEN Cannibals \cup Missionaries
                                            ELSE {}];
end algorithm; *)

\* Type correctness invariant
TypeOK == 
  /\ bank_of_boat \in {"E","W"}
  /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

\* Initial state
Init == 
  /\ bank_of_boat = "E"
  /\ who_is_on_bank = [i \in {"E","W"} |-> 
                         IF i = "E" THEN Cannibals \cup Missionaries ELSE {}]

\* Safety condition for a bank
IsSafe(S) == 
  \/ S \subseteq Cannibals
  \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

\* The opposite bank
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

\* A safe move of a set S of people from bank b to the other bank
Move(S, b) == 
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN /\ IsSafe(newThisBank)
        /\ IsSafe(newOtherBank)
        /\ bank_of_boat' = OtherBank(b)
        /\ who_is_on_bank' = 
             [i \in {"E","W"} |-> IF i = b THEN newThisBank ELSE newOtherBank]

\* Next-state relation
Next == 
  \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

\* State predicate that is true in the initial state and preserved by Next
FT == 
  /\ bank_of_boat = "E"
  /\ who_is_on_bank["E"] = Missionaries \cup Cannibals
  /\ who_is_on_bank["W"] = {}

\* The specification
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

\* Safety invariant required by TLC (the problem is solved when it becomes false)
Solution == who_is_on_bank["E"] /= {}

=============================================================================