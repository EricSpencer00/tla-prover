---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(* ------------------------------------------------------------------------- *)
(* TYPE INVARIANT                                                            *)
(* ------------------------------------------------------------------------- *)
TypeOK == /\ bank_of_boat \in {"E","W"}
          /\ who_is_on_bank \in [{"E","W"} -> SUBSET (Cannibals \cup Missionaries)]

(* ------------------------------------------------------------------------- *)
(* INITIAL STATE                                                            *)
(* ------------------------------------------------------------------------- *)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E","W"} |-> 
                               IF i = "E" THEN Cannibals \cup Missionaries
                                          ELSE {}]

(* ------------------------------------------------------------------------- *)
(* HELPERS                                                                   *)
(* ------------------------------------------------------------------------- *)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* ------------------------------------------------------------------------- *)
(* MOVE ACTION (fixed to keep the passenger on the destination bank)        *)
(* ------------------------------------------------------------------------- *)
Move(S, b) == /\ Cardinality(S) \in {1,2}
             /\ LET newThisBank  == who_is_on_bank[b] \ S
                    newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
                IN  /\ IsSafe(newThisBank)
                    /\ IsSafe(newOtherBank)
                    /\ bank_of_boat' = OtherBank(b)
                    /\ who_is_on_bank' = 
                         [i \in {"E","W"} |-> 
                            IF i = b THEN newThisBank 
                            ELSE newOtherBank]

(* ------------------------------------------------------------------------- *)
(* NEXT STATE RELATION                                                       *)
(* ------------------------------------------------------------------------- *)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* ------------------------------------------------------------------------- *)
(* SOLUTION INVARIANT (used for TLC to find a trace)                         *)
(* ------------------------------------------------------------------------- *)
Solution == who_is_on_bank["E"] /= {}

=============================================================================