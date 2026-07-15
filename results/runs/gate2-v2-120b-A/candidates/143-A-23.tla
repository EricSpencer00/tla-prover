---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, east, west

(* ----------------------------------------------------------------------
   Auxiliary definitions
   ---------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals

IsMissionary(p) == p \in Missionaries
IsCannibal(p) == p \in Cannibals

(* The set of people currently on the specified bank *)
Bank(b) == IF b = "East" THEN east ELSE west

(* A bank is safe if either it contains no missionaries, or the number of
   cannibals does not exceed the number of missionaries. *)
BankSafe(b) ==
  LET m == Cardinality({p \in Bank(b) : IsMissionary(p)})
      c == Cardinality({p \in Bank(b) : IsCannibal(p)})
  IN  (m = 0) \/ (c <= m)

(* The system is in a safe state when both banks are safe. *)
Safe == BankSafe("East") /\ BankSafe("West")

(* The boat always carries one or two people.  This invariant is called
   Solution in the .cfg. *)
Solution ==
  /\ boat \in {"East", "West"}
  /\ (Cardinality(east) + Cardinality(west) = 6)
  /\ (boat = "East" => Cardinality(east) = 6 - Cardinality(west))
  /\ (boat = "West" => Cardinality(west) = 6 - Cardinality(east))

(* ----------------------------------------------------------------------
   Initial state
   ---------------------------------------------------------------------- *)

Init ==
  /\ boat = "East"
  /\ east = Missionaries \cup Cannibals
  /\ west = {}
  /\ Safe

(* ----------------------------------------------------------------------
   Move action: one or two people cross the river
   ---------------------------------------------------------------------- *)

Move ==
  \E group \in SUBSET(Bank(boat)) :
    /\ group # {}
    /\ Cardinality(group) \in 1..2
    /\ LET src == boat
           dst == IF src = "East" THEN "West" ELSE "East"
           srcBank == IF src = "East" THEN east ELSE west
           dstBank == IF dst = "East" THEN east ELSE west
       IN  /\ srcBank' = srcBank \ group
           /\ dstBank' = dstBank \cup group
           /\ boat'   = dst
    /\ Safe

Next == Move

(* ----------------------------------------------------------------------
   Specification
   ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<boat, east, west>>

(* ----------------------------------------------------------------------
   Type correctness invariant (optional but useful)
   ---------------------------------------------------------------------- *)

TypeOK ==
  /\ boat \in {"East", "West"}
  /\ east \subseteq People
  /\ west \subseteq People
  /\ east \cup west = People
  /\ east \cap west = {}

=============================================================================