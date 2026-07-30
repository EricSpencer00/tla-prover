---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES bank, peopleOn

vars == <<bank, peopleOn>>

\* The count of missionaries on a given bank.
MissionaryCount(k) == Cardinality(Missionaries \cap peopleOn[k])

\* The count of cannibals on a given bank; computing it by subtraction
\* is safe because every person is either a missionary or a cannibal, never
\* both, so the two groups partition the population.
CannibalCount(k) == Cardinality(peopleOn[k]) - MissionaryCount(k)

\* A bank is safe if it has no missionaries (so there is nothing to outnumber)
\* or if cannibals are not in the majority there.
BankIsSafe(k) == MissionaryCount(k) = 0 \/ CannibalCount(k) <= MissionaryCount(k)

TypeOK ==
    /\ bank \in Banks
    /\ peopleOn \in [Banks -> SUBSET People]
    /\ \A k \in Banks : peopleOn[k] \subseteq People

Init ==
    /\ bank = "east"
    /\ peopleOn = [k \in Banks |-> IF k = "east" THEN People ELSE {}]

\* A crossing moves one or two people across and is only taken when both
\* banks remain safe afterwards; the boat never empties the departure bank
\* to a dangerous state, and it never carries nobody.
Move ==
    \E g \in SUBSET People :
        /\ g # {}
        /\ Cardinality(g) <= 2
        /\ g \subseteq peopleOn[bank]
        /\ LET other == IF bank = "east" THEN "west" ELSE "east" IN
             /\ peopleOn' = [peopleOn EXCEPT ![bank] = @ \ g, ![other] = @ \cup g]
             /\ bank' = other

Next == Move

Solution == \A k \in Banks : BankIsSafe(k)

====