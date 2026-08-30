---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
Boarding == {1, 2}

\* peopleAt[b] is the set of people standing on bank b; boatBank is where the
\* vessel is docked. The boat always carries 1 or 2 people and never runs empty.
VARIABLES peopleAt, boatBank

vars == <<peopleAt, boatBank>>

RECURSIVE CountSet(_)
CountSet(S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN 1 + CountSet(S \ {x})

TypeOK ==
    /\ peopleAt \in [Banks -> SUBSET People]
    /\ boatBank \in Banks

Init ==
    /\ peopleAt = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ boatBank = "east"

\* The move is feasible only if the resulting distribution on both banks is safe.
Move(g) ==
    /\ g \in Boarding
    /\ Cardinality(peopleAt[boatBank]) >= g
    /\ \E group \in SUBSET peopleAt[boatBank] :
        /\ Cardinality(group) = g
        /\ \A b \in Banks :
            LET na == IF b = boatBank THEN peopleAt[b] \ group ELSE peopleAt[b] \cup group
                mc == CountSet(na \cap Missionaries
                cc == CountSet(na \cap Cannibals
            IN \A b \in Banks :
                (CountSet(na \cap Missionaries) = 0) \/ (CountSet(na \cap Cannibals) <= CountSet(na \cap Missionaries))
        /\ peopleAt' = [b \in Banks |->
                            IF b = boatBank THEN peopleAt[b] \ group
                            ELSE IF b = (IF boatBank = "east" THEN "west" ELSE "east") THEN peopleAt[b] \cup group
                            ELSE peopleAt[b]]
    /\ boatBank' = (IF boatBank = "east" THEN "west" ELSE "east")

Next == \E g \in Boarding : Move(g)

Solution ==
    /\ \A b \in Banks :
        (CountSet(peopleAt[b] \cap Missionaries) = 0) \/ (CountSet(peopleAt[b] \cap Cannibals) <= CountSet(peopleAt[b] \cap Missionaries))
    /\ Cardinality(peopleAt["east"]) + Cardinality(peopleAt["west"]) = Cardinality(People)

Spec == Init /\ [][Next]_vars

TypeOKInv == TypeOK

====