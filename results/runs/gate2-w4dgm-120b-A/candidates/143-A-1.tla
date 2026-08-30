---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

\* People is the shared population pool, partitioned across the two banks.
People == Missionaries \cup Cannibals
BankOf(p) == IF p \in Missionaries THEN "missionary" ELSE "cannibal"

VARIABLES boatAt, peopleAt

vars == <<boatAt, peopleAt>>

RECURSIVE Tally(_, _)
Tally(f, S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN f[x] + Tally(f, S \ {x})

MissionaryCount(b) == Tally([p \in People |-> IF BankOf(p) = "missionary" THEN 1 ELSE 0], peopleAt[b])
CannibalCount(b)  == Tally([p \in People |-> IF BankOf(p) = "cannibal" THEN 1 ELSE 0], peopleAt[b])

\* The puzzle is solved when the east bank is empty (everyone is west).
Solved == peopleAt["east"] = {}

TypeOK ==
    /\ boatAt \in Banks
    /\ peopleAt \in [Banks -> SUBSET People]

Init ==
    /\ boatAt = "east"
    /\ peopleAt = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A safe move: the crossing group is non-empty, size-bounded, and leaves
\* both banks with no missionaries outnumbered by cannibals.
Move ==
    \E g \in SUBSET People :
        /\ g # {}
        /\ Cardinality(g) <= 2
        /\ g \subseteq peopleAt[boatAt]
        /\ MissionaryCount(boatAt) - Tally([p \in People |-> IF p \in g /\ BankOf(p) = "missionary" THEN 1 ELSE 0], peopleAt[boatAt]) >= 1
        /\ MissionaryCount(boatAt) - Tally([p \in People |-> IF p \in g /\ BankOf(p) = "missionary" THEN 1 ELSE 0], peopleAt[boatAt]) >=
           CannibalCount(boatAt) - Tally([p \in People |-> IF p \in g /\ BankOf(p) = "cannibal" THEN 1 ELSE 0], peopleAt[boatAt])
        /\ MissionaryCount(If boatAt = "east" Then "west" Else "east") + Tally([p \in People |-> IF p \in g /\ BankOf(p) = "missionary" THEN 1 ELSE 0], peopleAt[If boatAt = "east" Then "west" Else "east"]) >= 1
        /\ MissionaryCount(If boatAt = "east" Then "west" Else "east") + Tally([p \in People |-> IF p \in g /\ BankOf(p) = "missionary" THEN 1 ELSE 0], peopleAt[If boatAt = "east" Then "west" Else "east"]) >=
           CannibalCount(If boatAt = "east" Then "west" Else "east") + Tally([p \in People |-> IF p \in g /\ BankOf(p) = "cannibal" THEN 1 ELSE 0], peopleAt[If boatAt = "east" Then "west" ELSE "east"])
        /\ peopleAt' = [peopleAt EXCEPT ![boatAt] = @ \ g, ![If boatAt = "east" Then "west" ELSE "east"] = @ \cup g]
        /\ boatAt' = If boatAt = "east" Then "west" ELSE "east"

Next == Move

\* Every inhabited bank with missionaries on it must have at least as many
\* missionaries as cannibals; the boat is never empty or overloaded.
Solution ==
    /\ \A b \in Banks : (peopleAt[b] # {}) => MissionaryCount(b) >= CannibalCount(b)
    /\ \A b \in Banks : MissionaryCount(b) >= 1 => MissionaryCount(b) >= CannibalCount(b)
    /\ \A b \in Banks : peopleAt[b] # {} => (MissionaryCount(b) >= 1 \/ CannibalCount(b) >= 1)
====