---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

(***************************************************************************)
(* The module models the classic missionaries and cannibals problem.      *)
(* The state consists of the bank on which the boat is docked and a       *)
(* mapping that tells, for each bank, which people (cannibals or          *)
(* missionaries) are present there.                                        *)
(***************************************************************************)

CONSTANTS Missionaries, Cannibals

VARIABLES bank_of_boat, who_is_on_bank

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK == /\ bank_of_boat \in {"E", "W"}
          /\ who_is_on_bank \in [{"E", "W"} -> SUBSET (Cannibals \cup Missionaries)]

(***************************************************************************)
(* Initial state                                                          *)
(***************************************************************************)
Init == /\ bank_of_boat = "E"
        /\ who_is_on_bank = [i \in {"E", "W"} |-> IF i = "E"
                               THEN Cannibals \cup Missionaries
                               ELSE {}]

(***************************************************************************)
(* Helper definitions                                                     *)
(***************************************************************************)

(* Safety condition for a set of people on a bank *)
IsSafe(S) == \/ S \subseteq Cannibals
             \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

(* The opposite bank *)
OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* A safe move of a non‑empty set S (size 1 or 2) from bank b to the other bank *)
Move(S, b) == /\ Cardinality(S) \in {1, 2}
              /\ LET newThisBank  == who_is_on_bank[b] \ S
                     newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
                 IN  /\ IsSafe(newThisBank)
                     /\ IsSafe(newOtherBank)
                     /\ bank_of_boat' = OtherBank(b)
                     /\ who_is_on_bank' = [i \in {"E", "W"} |-> IF i = b
                                            THEN newThisBank
                                            ELSE newOtherBank]

(***************************************************************************)
(* Next-state relation                                                    *)
(***************************************************************************)
Next == \E S \in SUBSET who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(***************************************************************************)
(* Invariant that will be used by TLC to find a solution.                *)
(* It asserts that at all reachable states there is still someone on the  *)
(* east bank.  When TLC discovers a violation, the counter‑example       *)
(* corresponds to a successful crossing.                                   *)
(***************************************************************************)
Solution == who_is_on_bank["E"] /= {}

=============================================================================