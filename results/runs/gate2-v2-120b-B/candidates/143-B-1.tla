---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

(* ---------------------------------------------------------------------- *)
(* Constants representing the sets of missionaries and cannibals.         *)
(* ---------------------------------------------------------------------- *)
CONSTANTS Missionaries, Cannibals

(* ---------------------------------------------------------------------- *)
(* State variables                                                       *)
(*   bank_of_boat   : which bank the boat is currently docked at.        *)
(*   who_is_on_bank: a function mapping each bank to the set of people   *)
(*                   currently present on that bank.                     *)
(* ---------------------------------------------------------------------- *)
VARIABLES bank_of_boat, who_is_on_bank

(* ---------------------------------------------------------------------- *)
(* Type invariant (helps TLC, does not affect the logic of the model).    *)
(* ---------------------------------------------------------------------- *)
TypeOK ==
  /\ bank_of_boat \in {"E", "W"}
  /\ who_is_on_bank \in [ {"E", "W"} -> SUBSET (Cannibals \cup Missionaries) ]

(* ---------------------------------------------------------------------- *)
(* Initial state: everyone starts on the east bank, boat also on east.    *)
(* ---------------------------------------------------------------------- *)
Init ==
  /\ bank_of_boat = "E"
  /\ who_is_on_bank = [ i \in {"E", "W"} |-> IF i = "E" THEN Cannibals \cup Missionaries ELSE {} ]

(* ---------------------------------------------------------------------- *)
(* Helper definitions                                                    *)
(* ---------------------------------------------------------------------- *)
IsSafe(S) ==
  \/ S \subseteq Cannibals
  \/ Cardinality(S \cap Cannibals) =< Cardinality(S \cap Missionaries)

OtherBank(b) == IF b = "E" THEN "W" ELSE "E"

(* ---------------------------------------------------------------------- *)
(* Move(S, b) describes a safe move of a non‑empty set S of people from   *)
(* bank b to the opposite bank.  The boat must be on bank b, and the     *)
(* move must respect the capacity limit of 2 people.                     *)
(* ---------------------------------------------------------------------- *)
Move(S, b) ==
  /\ bank_of_boat = b
  /\ S \subseteq who_is_on_bank[b]
  /\ Cardinality(S) \in {1, 2}
  /\ LET newThisBank  == who_is_on_bank[b] \ S
         newOtherBank == who_is_on_bank[OtherBank(b)] \cup S
     IN  /\ IsSafe(newThisBank)
         /\ IsSafe(newOtherBank)
         /\ bank_of_boat' = OtherBank(b)
         /\ who_is_on_bank' = [ i \in {"E", "W"} |-> IF i = b THEN newThisBank ELSE newOtherBank ]

(* ---------------------------------------------------------------------- *)
(* Next permits any safe move from the bank where the boat currently     *)
(* resides.                                                               *)
(* ---------------------------------------------------------------------- *)
Next == \E S \subseteq who_is_on_bank[bank_of_boat] : Move(S, bank_of_boat)

(* ---------------------------------------------------------------------- *)
(* Specification (the behavior we are interested in checking).           *)
(* ---------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_<<bank_of_boat, who_is_on_bank>>

(* ---------------------------------------------------------------------- *)
(* Safety property: the solution is reached when the east bank becomes  *)
(* empty.  TLC will look for a violation of this invariant, which yields *)
(* a counterexample trace that solves the puzzle.                         *)
(* ---------------------------------------------------------------------- *)
Solution == who_is_on_bank["E"] = {}

=============================================================================