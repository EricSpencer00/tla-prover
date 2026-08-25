---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

VARIABLES boat, east, west

(*--------------------------------------------------------------------*)
(* Type correctness invariant                                           *)
(*--------------------------------------------------------------------*)
TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq Missionaries \cup Cannibals
    /\ west \subseteq Missionaries \cup Cannibals
    /\ east \cup west = Missionaries \cup Cannibals
    /\ east \cap west = {}

(*--------------------------------------------------------------------*)
(* Safety of a bank: either no missionaries or cannibals ≤ missionaries *)
(*--------------------------------------------------------------------*)
Safe(bank) ==
    LET m == { x \in bank : x \in Missionaries }
        c == { x \in bank : x \in Cannibals }
    IN ( Cardinality(m) = 0 ) \/ ( Cardinality(c) <= Cardinality(m) )

(*--------------------------------------------------------------------*)
(* Initial state                                                       *)
(*--------------------------------------------------------------------*)
Init ==
    /\ boat = "East"
    /\ east = Missionaries \cup Cannibals
    /\ west = {}

(*--------------------------------------------------------------------*)
(* One crossing of the boat (one or two people, never empty)          *)
(*--------------------------------------------------------------------*)
Next ==
    \/ \E p \subseteq east :
          /\ boat = "East"
          /\ Cardinality(p) \in 1..2
          /\ east' = east \ p
          /\ west' = west \cup p
          /\ boat' = "West"
          /\ Safe(east') /\ Safe(west')
    \/ \E p \subseteq west :
          /\ boat = "West"
          /\ Cardinality(p) \in 1..2
          /\ west' = west \ p
          /\ east' = east \cup p
          /\ boat' = "East"
          /\ Safe(east') /\ Safe(west')

(*--------------------------------------------------------------------*)
(* Solution condition: all people have reached the west bank          *)
(*--------------------------------------------------------------------*)
Solution == east = {}

====