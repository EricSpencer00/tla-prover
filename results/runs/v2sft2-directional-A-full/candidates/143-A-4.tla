---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES Boat, Bank

(*---------------------------------------------------------------------*)
(*  Helper definitions                                                 *)
(*---------------------------------------------------------------------*)

Banks == {"E", "W"}

AllPeople == Missionaries \cup Cannibals

(* Counts of missionaries and cannibals on a given bank *)
MissionariesOn(b) == {p \in Missionaries : p \in Bank[b]}
CannibalsOn(b)   == {p \in Cannibals   : p \in Bank[b]}

(* A bank is safe if it contains no missionaries or cannibals
   do not outnumber missionaries. *)
SafeBank(b) == (MissionariesOn(b) = {}) \/ (Cardinal(CannibalsOn(b)) <= Cardinal(MissionariesOn(b)))

(* Safety invariant required by the description *)
SafeState == \A b \in Banks : SafeBank(b)

(*---------------------------------------------------------------------*)
(*  Initial state                                                      *)
(*---------------------------------------------------------------------*)

Init ==
    /\ Boat = "E"
    /\ Bank = [b \in Banks |-> IF b = "E" THEN AllPeople ELSE {}]
    /\ SafeState

(*---------------------------------------------------------------------*)
(*  Move action: one or two people cross from the current bank to the
   opposite bank. The action is enabled only if the resulting state
   remains safe.                                                      *)
(*---------------------------------------------------------------------*)

Move ==
    \E group \in Subset(AllPeople, 1, 2) :
        /\ group \subseteq Bank[Boat]          \* people must be on the departure bank
        /\ \E newBoat \in Banks \ {Boat} :      \* the boat moves to the other bank
               /\ Boat' = newBoat
               /\ Bank' = [b \in Banks |-> 
                           IF b = Boat THEN Bank[b] \ group
                           ELSE IF b = newBoat THEN Bank[b] \cup group
                           ELSE Bank[b]]
               /\ SafeState

Next == Move

(*---------------------------------------------------------------------*)
(*  Type correctness invariant (required by the reference cfg)        *)
(*---------------------------------------------------------------------*)

TypeOK ==
    /\ Boat \in Banks
    /\ Bank \in [b \in Banks |-> SUBSET AllPeople]
    /\ \A b \in Banks : Bank[b] \subseteq AllPeople

(*---------------------------------------------------------------------*)
(*  Solution invariant: the puzzle is solved when the east bank is empty
   and all people are on the west bank.                                 *)
(*---------------------------------------------------------------------*)

Solution ==
    /\ Bank["E"] = {}
    /\ Bank["W"] = AllPeople
    /\ Boat = "W"

(*---------------------------------------------------------------------*)
(*  Specification                                                       *)
(*---------------------------------------------------------------------*)

Spec == Init /\ [][Next]_<<Boat, Bank>>

====