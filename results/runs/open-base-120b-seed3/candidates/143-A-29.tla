---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* Assume the two groups are disjoint *)
ASSUME Missionaries ∩ Cannibals = {}

(* The two river banks *)
BANK == {"East", "West"}

VARIABLES boat, people

(* --------------------------------------------------------------------- *)
(* Type correctness invariant                                            *)
(* --------------------------------------------------------------------- *)
TypeOK ==
  /\ boat ∈ BANK
  /\ people ∈ [BANK -> SUBSET (Missionaries ∪ Cannibals)]

(* --------------------------------------------------------------------- *)
(* Helper definitions                                                   *)
(* --------------------------------------------------------------------- *)
MissionariesIn(b) == people[b] ∩ Missionaries
CannibalsIn(b)   == people[b] ∩ Cannibals

Safe(b) ==
  /\ MissionariesIn(b) = {}
     \/ Cardinality(CannibalsIn(b)) <= Cardinality(MissionariesIn(b))

OtherBank(b) == IF b = "East" THEN "West" ELSE "East"

(* --------------------------------------------------------------------- *)
(* Initial state                                                         *)
(* --------------------------------------------------------------------- *)
Init ==
  /\ boat = "East"
  /\ people = [b ∈ BANK |-> IF b = "East"
                           THEN Missionaries ∪ Cannibals
                           ELSE {}]

(* --------------------------------------------------------------------- *)
(* One crossing of the boat (one or two people)                         *)
(* --------------------------------------------------------------------- *)
Move ==
  ∃ g ⊆ people[boat] :
    /\ Cardinality(g) ∈ 1..2
    /\ LET ob == OtherBank(boat) IN
         /\ boat'   = ob
         /\ people' = [people EXCEPT
                         ![boat] = people[boat] \ g,
                         ![ob]   = people[ob]   ∪ g]
    /\ ∀ b ∈ BANK : Safe(b)

Next == Move

(* --------------------------------------------------------------------- *)
(* Invariant that is violated exactly when the puzzle is solved          *)
(* --------------------------------------------------------------------- *)
Solution ==
  people["East"] # {}

=============================================================================