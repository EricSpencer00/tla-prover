---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \union Cannibals

VARIABLES boatAt, bank
vars == <<boatAt, bank>>

TypeOK ==
    /\ boatAt \in Banks
    /\ bank \in [Banks -> SUBSET People]

Init ==
    /\ boatAt = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Counts(b) ==
    LET mc == Cardinality(bank[b] \intersect Missionaries)
        cc == Cardinality(bank[b] \intersect Cannibals)
    IN [missionaries |-> mc, cannibals |-> cc]

Solution == bank["east"] = {}

Move ==
    /\ \E group \in SUBSET BankAt(boatAt) :
         /\ Cardinality(group) \in {1, 2}
         /\ Cardinality(group) >= 1
         /\ LET src == boatAt
                dst == IF boatAt = "east" THEN "west" ELSE "east"
                newBank == [bank EXCEPT ![src] = bank[src] \ group, ![dst] = bank[dst] \union group]
                srcCounts == Counts(src)
                dstCounts == Counts(dst)
            IN /\ (srcCounts.missionaries = 0 \/ srcCounts.cannibals <= srcCounts.missionaries)
               /\ (dstCounts.missionaries = 0 \/ dstCounts.cannibals <= dstCounts.missionaries)
               /\ bank' = newBank
               /\ boatAt' = dst

BankAt(b) == bank[b]

Next == Move

TypeOK == TypeOK

Solution == Solution

====