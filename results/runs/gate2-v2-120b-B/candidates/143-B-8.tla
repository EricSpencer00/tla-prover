---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(*--- Type correctness invariant ---*)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(*--- Initial state ---*)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE {}]

(*--- Safety of a bank ---*)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(*--- Helper to get the opposite bank ---*)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(*--- One move of a set S from bank b ---*)
Move(S, b) == 
    LET newThisBank  == who_is_on_bank[b] \ S
        newOtherBank == (who_is_on_bank[OtherBank(b)] \cup S) \cap (who_is_on_bank[OtherBank(b)] \cup S) 
    IN
    /\ Cardinality(S) \in {1, 2}
    /\ newThisBank = who_is_on_bank[b] \ S
    /\ newOtherBank = who_is_on_bank[OtherBank(b)] \cup S
    /\ IsSafe(newThisBank)
    /\ IsSafe(newOtherBank)
    /\ bank_of_boat' = OtherBank(b)
    /\ who_is_on_bank' = [i \in {"E","W"} |-> 
                            IF i = b THEN newThisBank 
                            ELSE IF i = OtherBank(b) THEN newOtherBank 
                            ELSE who_is_on_bank[i]]

(*--- Next-state relation ---*)
Next == 
    \E S \in SUBSET (who_is_on_bank[bank_of_boat]) : 
        /\ S # {}
        /\ Move(S, bank_of_boat)

(*--- Safety invariant used during model checking ---*)
SolutionInvariant == who_is_on_bank["E"] = {}

(*--- The specification's behavior ---*)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

=============================================================================