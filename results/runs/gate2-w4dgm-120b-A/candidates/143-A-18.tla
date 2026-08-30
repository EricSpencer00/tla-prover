---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, peopleAt

vars == <<boatAt, peopleAt>>

TypeOK ==
    /\ boatAt \in Banks
    /\ peopleAt \in [Banks -> SUBSET Missionaries \cup Cannibals]

Init ==
    /\ boatAt = "east"
    /\ peopleAt = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

GroupFitsBank(g, b) ==
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ g \subseteq peopleAt[b]

UpdateBank(b, g) ==
    [peopleAt[b] EXCEPT ! = @ \ g]

AddToBank(b, g) ==
    [peopleAt[b] EXCEPT ! = @ \cup g]

Move(g) ==
    /\ GroupFitsBank(g, boatAt)
    /\ \A k \in Banks : Cardinality(peopleAt[k]) >= Cardinality(g \cap peopleAt[k])
    /\ LET other == IF boatAt = "east" THEN "west" ELSE "east" IN
        /\ peopleAt' = AddToBank(other, g) @@ UpdateBank(boatAt, g)
        /\ boatAt' = other

Next ==
    \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

Safety ==
    /\ \A k \in Banks :
        (peopleAt[k] \cap Missionaries # {}) => (Cardinality(peopleAt[k] \cap Cannibals) <= Cardinality(peopleAt[k] \cap Missionaries))
    /\ \A k \in Banks : Cardinality(peopleAt[k] \cap (Missionaries \cup Cannibals)) <= 3

Solution == \A k \in Banks : peopleAt[k] \cap Missionaries = {}

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A g \in SUBSET (Missionaries \cup Cannibals) : WF_vars(Move(g))

====