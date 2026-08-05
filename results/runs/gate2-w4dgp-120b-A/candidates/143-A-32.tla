---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

VARIABLES boat, banks

vars == <<boat, banks>>

Bump(x) == IF x < 2 THEN x + 1 ELSE 2

TypeOK ==
    /\ boat \in {"east", "west"}
    /\ banks \in [east: SUBSET People, west: SUBSET People]

Init ==
    /\ boat = "east"
    /\ banks = [east |-> People, west |-> {}]

\* The river crossing can never be run empty: a move must carry at least one
\* and at most two people.
Move(g) ==
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ g \subseteq banks[boat]
    /\ banks' = [boat |-> banks[boat] \ g, boat \cup g |-> banks[boat \cup g] \cup g]
    /\ boat' = boat \cup g
    /\ \A side \in {"east", "west"} :
         ~ /\ banks'[side] # {}
            /\ banks'[side] \cap Missionaries # {}
            /\ Cardinality(banks'[side] \cap Cannibals) > Cardinality(banks'[side] \cap Missionaries)
         \/ /\ banks'[side] # {}
            /\ banks'[side] \cap Missionaries = {}
            /\ Cardinality(banks'[side] \cap Cannibals) > 0

Next == \E g \in SUBSET People : Move(g)

\* Safety: neither bank ever has missionaries outnumbered by cannibals.
Solution ==
    /\ \A side \in {"east", "west"} :
         ~ /\ banks[side] # {}
            /\ banks[side] \cap Missionaries # {}
            /\ Cardinality(banks[side] \cap Cannibals) > Cardinality(banks[side] \cap Missionaries)
         \/ /\ banks[side] # {}
            /\ banks[side] \cap Missionaries = {}
            /\ Cardinality(banks[side] \cap Cannibals) > 0
    /\ banks["east"] = {}

====