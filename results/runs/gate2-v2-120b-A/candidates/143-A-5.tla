---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

(*-------------------------------------------------------------------*)
(* Derived constant sets for convenience                               *)
(*-------------------------------------------------------------------*)
MissionarySet == Missionaries
CannibalSet   == Cannibals

(*-------------------------------------------------------------------*)
(* State variables                                                    *)
(*-------------------------------------------------------------------*)
VARIABLES boat, east, west

(*-------------------------------------------------------------------*)
(* Helper definitions                                                 *)
(*-------------------------------------------------------------------*)
People == MissionarySet \cup CannibalSet

Side == {"East", "West"}

(* The set of people on the current bank of the boat *)
CurrentBank == IF boat = "East" THEN east ELSE west

(* The set of people on the opposite bank *)
OppositeBank == IF boat = "East" THEN west ELSE east

(* Count of missionaries on a given bank *)
MissionariesOn(s) == Cardinality({p \in s : p \in MissionarySet})

(* Count of cannibals on a given bank *)
CannibalsOn(s) == Cardinality({p \in s : p \in CannibalSet})

(* Safety condition for a given bank *)
SafeBank(s) ==
    \A m \in s : m \in MissionarySet => 
        (\E c \in s : c \in CannibalSet) => 
            MissionariesOn(s) >= CannibalsOn(s)

(* Safety of the whole configuration *)
Safe == SafeBank(east) /\ SafeBank(west)

(*-------------------------------------------------------------------*)
(* Initial state                                                      *)
(*-------------------------------------------------------------------*)
Init ==
    /\ boat = "East"
    /\ east = People
    /\ west = {}

(*-------------------------------------------------------------------*)
(* Move action definition                                             *)
(*-------------------------------------------------------------------*)
Move ==
    \E gr \in SUBSET CurrentBank :
        /\ Cardinality(gr) \in 1..2
        /\ east' = IF boat = "East"
                     THEN east \ SetMinus gr
                     ELSE east \cup gr
        /\ west' = IF boat = "West"
                     THEN west \ SetMinus gr
                     ELSE west \cup gr
        /\ boat' = IF boat = "East" THEN "West" ELSE "East"
        /\ Safe

Next == Move

(*-------------------------------------------------------------------*)
(* Specification (for completeness, not required by cfg)             *)
(*-------------------------------------------------------------------*)
Spec == Init /\ [][Next]_<<boat, east, west>>

(*-------------------------------------------------------------------*)
(* Type correctness invariant                                         *)
(*-------------------------------------------------------------------*)
TypeOK ==
    /\ boat \in Side
    /\ east \subseteq People
    /\ west \subseteq People
    /\ east \cup west = People
    /\ east \cap west = {}

(*-------------------------------------------------------------------*)
(* Solution (liveness) invariant: all people have reached the West   *)
(*-------------------------------------------------------------------*)
Solution == east = {}

=============================================================================