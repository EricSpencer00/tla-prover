---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* ------------------------------------------------------------------------ *)
(* Type correctness invariant                                               *)
(* ------------------------------------------------------------------------ *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [ {"E","W"} -> SUBSET (Missionaries \cup Cannibals) ]

(* ------------------------------------------------------------------------ *)
(* Initial state: everyone starts on the east bank                           *)
(* ------------------------------------------------------------------------ *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> IF i = "E"
                                            THEN Missionaries \cup Cannibals
                                            ELSE {}]

(* ------------------------------------------------------------------------ *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------ *)
IsSafe(S) == \/ S \subseteq Missionaries
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* ------------------------------------------------------------------------ *)
(* A move of a non‑empty set S (size 1 or 2) from bank b to the opposite      *)
(* bank, provided the resulting banks are safe.                              *)
(* ------------------------------------------------------------------------ *)
Move(S, b) ==
    /\ Cardinality(S) \in {1, 2}
    /\ LET newThisBank  == who_is_on_bank[b] \ S
           newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
       IN /\ IsSafe(newThisBank)
          /\ IsSafe(newOtherBank)
          /\ bank_of_boat' = OtherBank(b)
          /\ who_is_on_bank' = [i \in {"E","W"} |-> IF i = b THEN newThisBank
                                                          ELSE newOtherBank]

(* ------------------------------------------------------------------------ *)
(* Next-state relation: any safe move of a subset of the current boat bank   *)
(* ------------------------------------------------------------------------ *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* ------------------------------------------------------------------------ *)
(* Safety invariant: the state where everyone has crossed is never reached   *)
(* (TLC will report a deadlock when it tries to leave that state).          *)
(* ------------------------------------------------------------------------ *)
NoAllCrossed == ~ (who_is_on_bank["E"] = {})

(* ------------------------------------------------------------------------ *)
(* Full specification                                                       *)
(* ------------------------------------------------------------------------ *)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

====