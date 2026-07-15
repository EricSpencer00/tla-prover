---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------------- *)
(* Derived constant sets and auxiliary definitions                     *)
(* ------------------------------------------------------------------- *)

People == Missionaries \cup Cannibals

East == "East"
West == "West"

Banks == {East, West}

(* ------------------------------------------------------------------- *)
(* State variables                                                    *)
(* ------------------------------------------------------------------- *)

VARIABLES boat, location

(* ------------------------------------------------------------------- *)
(* Helper definitions                                                 *)
(* ------------------------------------------------------------------- *)

(* People on a given bank *)
PeopleOn(b) == IF b = East THEN location ELSE (People \ location)

(* Number of missionaries on a bank *)
MCount(b) == Cardinality({ p \in PeopleOn(b) : p \in Missionaries })

(* Number of cannibals on a bank *)
CCount(b) == Cardinality({ p \in PeopleOn(b) : p \in Cannibals })

(* Safety condition for a single bank *)
SafeBank(b) ==
    /\ (MCount(b) = 0) \/ (CCount(b) <= MCount(b))

(* Global safety condition *)
Safe == /\ SafeBank(East) /\ SafeBank(West)

(* The set of all possible groups that can travel (1 or 2 people) *)
TravelGroups ==
    { g \in SUBSET People :
        Cardinality(g) \in 1..2 }

(* A group g is a legal move from the current bank if all its members are present there *)
LegalMove(g) == g \subseteq PeopleOn(boat)

(* ------------------------------------------------------------------- *)
(* Initial state                                                      *)
(* ------------------------------------------------------------------- *)

Init ==
    /\ boat = East
    /\ location = Missionaries \cup Cannibals
    /\ Safe

(* ------------------------------------------------------------------- *)
(* Next-state relation                                                *)
(* ------------------------------------------------------------------- *)

Next ==
    \E g \in TravelGroups :
        /\ LegalMove(g)
        /\ LET newLoc == location \ g \cup (g \ { p : p \in g /\ p \notin location })
           IN /\ location' = newLoc
              /\ boat' = IF boat = East THEN West ELSE East
              /\ Safe
        /\ UNCHANGED << >>

(* ------------------------------------------------------------------- *)
(* Specification                                                      *)
(* ------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_<<location, boat>>

(* ------------------------------------------------------------------- *)
(* Invariants                                                         *)
(* ------------------------------------------------------------------- *)

(* Type correctness: all variables range over their intended domains *)
TypeOK ==
    /\ boat \in Banks
    /\ location \subseteq People
    /\ Safe

(* Solution: the east bank is empty *)
Solution == location = {}

=============================================================================