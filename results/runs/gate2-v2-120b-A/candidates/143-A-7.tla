---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------- *)
(*   State variables                                                 *)
(* ------------------------------------------------------------------- *)
VARIABLES boat, east, west

(* ------------------------------------------------------------------- *)
(*   Derived collections                                             *)
(* ------------------------------------------------------------------- *)
People == Missionaries \cup Cannibals

(* ------------------------------------------------------------------- *)
(*   Helper definitions                                              *)
(* ------------------------------------------------------------------- *)

(* The set of all people currently on a given bank *)
BankPeople(b) == IF b = "east" THEN east ELSE west

(* Number of missionaries on a given bank *)
MCount(b) == Cardinality({ p \in BankPeople(b) : p \in Missionaries })

(* Number of cannibals on a given bank *)
CCount(b) == Cardinality({ p \in BankPeople(b) : p \in Cannibals })

(* Safety condition for a single bank *)
SafeBank(b) == (MCount(b) = 0) \/ (CCount(b) <= MCount(b))

(* Overall safety condition *)
Safe == SafeBank("east") /\ SafeBank("west")

(* The set of all possible groups that can board the boat:
   one or two people from the current bank *)
BoardingGroups(b) ==
  { g \in SUBSET BankPeople(b) :
      Cardinality(g) \in 1..2 }

(* ------------------------------------------------------------------- *)
(*   Initial state                                                   *)
(* ------------------------------------------------------------------- *)
Init ==
  /\ boat = "east"
  /\ east = Missionaries \cup Cannibals
  /\ west = {}

(* ------------------------------------------------------------------- *)
(*   Move action                                                     *)
(* ------------------------------------------------------------------- *)
Move ==
  \E g \in BoardingGroups(boat) :
    LET dest == IF boat = "east" THEN "west" ELSE "east"
        newEast == IF boat = "east"
                    THEN east \ g
                    ELSE east \cup g
        newWest == IF boat = "west"
                    THEN west \ g
                    ELSE west \cup g
    IN
      /\ newEast \subseteq People
      /\ newWest \subseteq People
      /\ newEast \cup newWest = People
      /\ /\ boat' = dest
         /\ east' = newEast
         /\ west' = newWest
      /\ Safe

Next == Move

(* ------------------------------------------------------------------- *)
(*   Variables tuple (required by TLC)                               *)
(* ------------------------------------------------------------------- *)
vars == <<boat, east, west>>

(* ------------------------------------------------------------------- *)
(*   Type correctness invariant                                      *)
(* ------------------------------------------------------------------- *)
TypeOK ==
  /\ boat \in {"east", "west"}
  /\ east \subseteq People
  /\ west \subseteq People
  /\ east \cup west = People
  /\ east \cap west = {}

(* ------------------------------------------------------------------- *)
(*   Safety / solution invariant (as described in the task)         *)
(* ------------------------------------------------------------------- *)
Solution == Safe

(* ------------------------------------------------------------------- *)
(*   The specification                                                *)
(* ------------------------------------------------------------------- *)
Spec == Init /\ [][Next]_vars

====