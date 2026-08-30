---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, bankOf

vars == <<boatAt, bankOf>>

TypeOK ==
    /\ boatAt \in Banks
    /\ bankOf \in [People -> Banks]

Init ==
    /\ boatAt = "east"
    /\ bankOf = [p \in People |-> "east"]

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(b) ==
    LET ms == {p \in Missionaries : bankOf[p] = b}
        cs == {p \in Cannibals : bankOf[p] = b}
    IN (ms = {}) \/ (Cardinality(cs) <= Cardinality(ms))

\* The boat carries one or two people; it never travels empty.
Move(g) ==
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ \A p \in g : bankOf[p] = boatAt
    /\ \A p \in g : bankOf' = [bankOf EXCEPT ![p] = IF boatAt = "east" THEN "west" ELSE "east"]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
    /\ BankSafe("east")
    /\ BankSafe("west")

Next == \E g \in SUBSET People : Move(g)

Spec == Init /\ [][Next]_vars

\* The east bank is never empty until the puzzle is solved; a violation is a
\* solution trace, not a deadlock.
Solution == \A p \in Missionaries \cup Cannibals : bankOf[p] = "west"

TypeOKInv == TypeOK

====