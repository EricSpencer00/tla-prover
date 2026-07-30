---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
AllPeople == Missionaries \cup Cannibals
NoOne == "empty"

VARIABLES boatAt, people
vars == <<boatAt, people>>

Eats(m, c) == Cardinality(c) > Cardinality(m)
\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
Safe(b) == (people[b] \cap Missionaries = {}) \/ ~Eats(people[b] \cap Missionaries, people[b] \cap Cannibals)

TypeOK == /\ boatAt \in Banks
          /\ people \in [Banks -> SUBSET AllPeople]
          /\ Cardinality(people["east"]) + Cardinality(people["west"]) = 6

Init == /\ boatAt = "east"
        /\ people = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]

\* Move: a group of size 1 or 2 boards the boat at the current bank and crosses,
\* landing on the other bank with a distribution that remains safe.
Move(g) == /\ g # {}
           /\ Cardinality(g) <= 2
           /\ g \subseteq people[boatAt]
           /\ LET other == IF boatAt = "east" THEN "west" ELSE "east" IN
                /\ ~Eats(people[boatAt] \ g \cup (people[other] \cup g), people[boatAt] \ g \cup (people[other] \cup g))
                /\ boatAt' = other
                /\ people' = [boatAt |-> people[boatAt] \ g, other |-> people[other] \cup g]
              

Next == \E g \in SUBSET AllPeople : Move(g)

\* The solution is a state in which the east bank is empty; checking that the
\* east bank is never empty would force a model checker to produce a crossing
\* trace as a counterexample.
Solution == people["east"] = {}

Spec == Init /\ [][Next]_vars

\* Safety: banks never endanger missionaries, and the boat always carries 1 or 2.
MissionarySafety == \A b \in Banks : Safe(b)
BoatLoads != 0
====