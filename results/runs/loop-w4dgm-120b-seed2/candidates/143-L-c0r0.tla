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

\* The boat carries at least one and at most two people; it never travels empty.
Move ==
    \E g \in SUBSET People :
        /\ g # {}
        /\ Cardinality(g) <= 2
        /\ \A p \in g : bankOf[p] = boatAt
        /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east"
               newBankOf == [q \in People |-> IF q \in g THEN dest ELSE bankOf[q]]
           IN /\ BankSafe(boatAt)
              /\ BankSafe(dest)
              /\ bankOf' = newBankOf
              /\ boatAt' = dest

Next == Move

Spec == Init /\ [][Next]_vars

\* The east bank is never empty until the puzzle is solved, so a violation
\* yields a concrete solution trace rather than a deadlock.
Solution == (bankOf' = [p \in People |-> "west"]) \/ (bankOf # [p \in People |-> "west"])

TypeOKInv == TypeOK
SolutionInv == Solution

INVARIANT TypeOKInv
INVARIANT SolutionInv
====