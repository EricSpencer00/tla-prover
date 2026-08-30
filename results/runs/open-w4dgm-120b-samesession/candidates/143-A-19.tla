---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"west", "east"}

VARIABLES boatAt, peopleAt

vars == <<boatAt, peopleAt>>

TypeOK ==
    /\ boatAt \in Banks
    /\ peopleAt \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
    /\ boatAt = "east"
    /\ peopleAt = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

Move ==
    /\ \E g \in SUBSET (Missionaries \cup Cannibals) :
         /\ Cardinality(g) \in {1, 2}
         /\ g \subseteq peopleAt[boatAt]
         /\ \E dest \in Banks :
              /\ dest # boatAt
              /\ \A b \in Banks : peopleAt[b] \ {g} \cup (IF b = dest THEN g ELSE {})
              /\ \A b \in Banks :
                   \/ peopleAt[b] \ {g} \cup (IF b = dest THEN g ELSE {}) \cap Missionaries = {}
                   \/ Cardinality(peopleAt[b] \ {g} \cup (IF b = dest THEN g ELSE {}) \cap Cannibals)
                        <= Cardinality(peopleAt[b] \ {g} \cup (IF b = dest THEN g ELSE {}) \cap Missionaries)
         /\ boatAt' = dest
         /\ peopleAt' = [b \in Banks |-> peopleAt[b] \ {g} \cup (IF b = dest THEN g ELSE {})]

Next == Move

Solution == \A b \in Banks : peopleAt[b] \cap Missionaries = {}

TypeOKInv == TypeOK

SolutionInv == Solution

Spec == Init /\ [][Next]_vars
====