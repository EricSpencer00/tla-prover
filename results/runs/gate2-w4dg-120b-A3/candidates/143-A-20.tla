---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

BANKS == {"east", "west"}

VARIABLES boatAt, bank

vars == <<boatAt, bank>>

Bump(x) == IF x = "east" THEN "west" ELSE "east"

RECURSIVE SumCount(_, _)
SumCount(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumCount(f, S \ {x})

People == Missionaries \cup Cannibals
BankPeople(b) == {p \in People : bank[p] = b}

TypeOK ==
    /\ boatAt \in BANKS
    /\ bank \in [People -> BANKS]

\* "Safe" is the missionaries-and-cannibals condition: either no
\* missionaries on the bank, or cannibals do not outnumber them.
BankSafe(b) ==
    LET M == SumCount([p \in People |-> IF p \in Missionaries THEN 1 ELSE 0], BankPeople(b))
        C == SumCount([p \in People |-> IF p \in Cannibals THEN 1 ELSE 0], BankPeople(b))
    IN M = 0 \/ C <= M

Solution ==
    /\ BankSafe("east")
    /\ BankSafe("west")
    /\ Cardinality(BankPeople("east")) > 0

Init ==
    /\ boatAt = "east"
    /\ bank = [p \in People |-> "east"]

\* One or two people board the boat on its current bank, cross to the other
\* bank, and disembark. The resulting banks must both still be safe.
Next ==
    \/ \E g \in SUBSET People :
         /\ g # {}
         /\ Cardinality(g) <= 2
         /\ \A p \in g : bank[p] = boatAt
         /\ LET newBank == [p \in People |-> IF p \in g THEN Bump(boatAt) ELSE bank[p]]
            IN /\ BankSafe(Bump(boatAt))
               /\ BankSafe(boatAt)
               /\ bank' = newBank
         /\ boatAt' = Bump(boatAt)
    \/ UNCHANGED <<boatAt, bank>>

Spec == Init /\ [][Next]_vars

====