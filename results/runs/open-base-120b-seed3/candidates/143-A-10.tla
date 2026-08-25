---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ----------------------------------------------------------------------
   Derived constants
   ---------------------------------------------------------------------- *)
AllPeople == Missionaries \cup Cannibals
BANK == {"East", "West"}

VARIABLES b, east, west

(* ----------------------------------------------------------------------
   Type invariant
   ---------------------------------------------------------------------- *)
TypeOK ==
  /\ b \in BANK
  /\ east \subseteq AllPeople
  /\ west \subseteq AllPeople
  /\ east \cup west = AllPeople
  /\ east \cap west = {}

(* ----------------------------------------------------------------------
   Safety of a bank: either no missionaries or cannibals do not outnumber them
   ---------------------------------------------------------------------- *)
SafeBank(s) ==
  LET m == Missionaries \cap s
      c == Cannibals \cap s
  IN (m = {} ) \/ (Cardinality(c) <= Cardinality(m))

Safe == SafeBank(east) /\ SafeBank(west)

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)
Init ==
  /\ b = "East"
  /\ east = AllPeople
  /\ west = {}

(* ----------------------------------------------------------------------
   Move action: transport 1 or 2 people, keep safety, flip boat location
   ---------------------------------------------------------------------- *)
Move ==
  \E grp \subseteq (IF b = "East" THEN east ELSE west):
    /\ Cardinality(grp) \in 1..2
    /\ LET newEast ==
           IF b = "East" THEN east \ grp ELSE east \cup grp
         newWest ==
           IF b = "West" THEN west \ grp ELSE west \cup grp
       IN /\ east' = newEast
          /\ west' = newWest
          /\ b' = IF b = "East" THEN "West" ELSE "East"
          /\ Safe

Next == Move

(* ----------------------------------------------------------------------
   Solution invariant: the east bank must stay non‑empty.
   Its violation corresponds to solving the puzzle.
   ---------------------------------------------------------------------- *)
Solution == east # {}

====