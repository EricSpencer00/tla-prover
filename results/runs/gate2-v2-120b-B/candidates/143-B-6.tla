---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals 

VARIABLES bank_of_boat, who_is_on_bank 

(* Type correctness invariant *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in 
                [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(* Initial state: everyone on the east bank *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE {}]

(* Safety condition for a set of people on a bank *)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(* The opposite bank *)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* Move a set S of people from bank b to the opposite bank *)
Move(S, b) == 
    /\ Cardinality(S) \in {1,2}
    /\ LET newThisBank  == who_is_on_bank[b] \ S
           newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
       IN /\ IsSafe(newThisBank)
          /\ IsSafe(newOtherBank)
          /\ bank_of_boat' = OtherBank(b)
          /\ who_is_on_bank' = 
                [i \in {"E","W"} |-> 
                    IF i = b THEN newThisBank 
                    ELSE IF i = OtherBank(b) THEN newOtherBank 
                    ELSE who_is_on_bank[i]]

(* Next-state relation: any safe move from the current boat bank *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* The property used to find a solution: eventually everyone is on the west bank *)
Solution == who_is_on_bank["E"] = {}

=============================================================================