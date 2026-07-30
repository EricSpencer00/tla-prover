---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Missionaries,
    Cannibals

\* Banks are named east and west; the boat docks at exactly one of them.
Banks == {"east", "west"}
zombies == Missionaries \cup Cannibals
None == "none"

VARIABLES
    boatAt,
    people

vars == <<boatAt, people>>

\* SafeBank is the classic missionaries-vs-cannibals safety rule: a bank
\* with missionaries must not have more cannibals than missionaries.
TypeOK ==
    /\ boatAt \in Banks
    /\ people \in [Banks -> SUBSET zombies]

\* Both banks must be safe, and the boat must always carry one or two people.
Solution ==
    /\ \A b \in Banks :
         \/ people[b] \cap Missionaries = {}
         \/ Cardinality(people[b] \cap Cannibals) <= Cardinality(people[b] \cap Missionaries)
    /\ Cardinality(people["east"]) + Cardinality(people["west"]) = 6

Init ==
    /\ boatAt = "east"
    /\ people = [b \in Banks |-> IF b = "east" THEN zombies ELSE {}]

\* The move is choreographed as a single atomic state transition: the chosen
\* people leave the departure bank and appear on the arrival bank in one step.
Move(g) ==
    /\ g \subseteq people[boatAt]
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ \/ Missionaries \cap g = {}
       \/ Cardinality(g \cap Missionaries) >= Cardinality(g \cap Cannibals)
    /\ LET other == IF boatAt = "east" THEN "west" ELSE "east" IN
         /\ people' = [people EXCEPT ![boatAt] = people[boatAt] \ g, ![other] = people[other] \cup g]
         /\ boatAt' = other

Next ==
    \/ \E g \in SUBSET zombies : Move(g)

Spec == Init /\ [][Next]_vars

====