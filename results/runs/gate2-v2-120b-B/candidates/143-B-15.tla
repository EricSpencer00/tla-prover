---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* --------------------------------------------------------------------- *)
(* Type invariant                                                       *)
(* --------------------------------------------------------------------- *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Missionaries \cup Cannibals)]

(* --------------------------------------------------------------------- *)
(* Initial state                                                        *)
(* --------------------------------------------------------------------- *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Missionaries \cup Cannibals 
                                         ELSE {}]

(* --------------------------------------------------------------------- *)
(* Helper definitions                                                   *)
(* --------------------------------------------------------------------- *)
IsSafe(S) == \/ S \subseteq Missionaries
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

Move(S, b) == 
    LET newThisBank  == who_is_on_bank[b] \ S
        newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
    IN /\ Cardinality(S) \in {1, 2}
       /\ IsSafe(newThisBank)
       /\ IsSafe(newOtherBank)
       /\ bank_of_boat' = OtherBank(b)
       /\ who_is_on_bank' = 
            [i \in {"E","W"} |-> IF i = b THEN newThisBank 
                                         ELSE newOtherBank]

(* --------------------------------------------------------------------- *)
(* Next-state relation                                                   *)
(* --------------------------------------------------------------------- *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* --------------------------------------------------------------------- *)
(* Safety invariant (ensures progress toward solution)                 *)
(* --------------------------------------------------------------------- *)
MissionariesAndCannibalsSafety == 
    /\ who_is_on_bank["E"] = {}
       => who_is_on_bank["W"] = Missionaries \cup Cannibals

(* --------------------------------------------------------------------- *)
(* Specification                                                        *)
(* --------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

=============================================================================