---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES BoatLoc, East, West

(* ------------------------------------------------------------------ *)
(* Universe of people *)
AllPeople == Missionaries \cup Cannibals

(* ------------------------------------------------------------------ *)
(* Safety predicate for a bank *)
IsSafe(bank) ==
  LET m == Cardinality(bank \cap Missionaries) ;
      c == Cardinality(bank \cap Cannibals)
  IN (m = 0) \/ (c <= m)

(* ------------------------------------------------------------------ *)
(* Type correctness invariant *)
TypeOK ==
  /\ BoatLoc \in {"East", "West"}
  /\ East \subseteq AllPeople
  /\ West \subseteq AllPeople
  /\ East \cap West = {}
  /\ East \cup West = AllPeople

(* ------------------------------------------------------------------ *)
(* Initial state *)
Init ==
  /\ BoatLoc = "East"
  /\ East = AllPeople
  /\ West = {}

(* ------------------------------------------------------------------ *)
(* One crossing of the boat *)
Move ==
  LET CurrentBank == IF BoatLoc = "East" THEN East ELSE West
  IN  \E persons \subseteq CurrentBank :
        /\ Cardinality(persons) \in {1, 2}
        /\ LET newEast == IF BoatLoc = "East" THEN East \ persons ELSE East \cup persons ;
               newWest == IF BoatLoc = "East" THEN West \cup persons ELSE West \ persons
           IN /\ BoatLoc' = (IF BoatLoc = "East" THEN "West" ELSE "East")
              /\ East' = newEast
              /\ West' = newWest
              /\ IsSafe(newEast)
              /\ IsSafe(newWest)

(* ------------------------------------------------------------------ *)
(* Next-state relation *)
Next == Move

(* ------------------------------------------------------------------ *)
(* Full specification *)
Spec == Init /\ [][Next]_<<BoatLoc, East, West>>

(* ------------------------------------------------------------------ *)
(* Invariant that is expected to be violated when the puzzle is solved *)
Solution == East # {}

====