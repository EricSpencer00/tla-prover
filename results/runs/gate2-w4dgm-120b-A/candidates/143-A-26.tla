---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, people

vars == <<boatAt, people>>

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumSet(f, S \ {x})

TypeOK ==
    /\ boatAt \in Banks
    /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
    /\ \A b \in Banks : people[b] # {}

BankOK(b) ==
    LET mCount == Cardinality(people[b] \cap Missionaries)
        cCount == Cardinality(people[b] \cap Cannibals)
    IN (mCount = 0) \/ (cCount <= mCount)

\* The safety condition: no missionaries are ever outnumbered on a bank where
\* they are present.
Safety == \A b \in Banks : BankOK(b)

Init ==
    /\ boatAt = "east"
    /\ people = [b \in Banks |-> IF b = "east" THEN (Missionaries \cup Cannibals) ELSE {}]

\* A crossing must land on a safe configuration on both banks.
MoveGroup(g) ==
    /\ g \subseteq people[boatAt]
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ LET dest == (IF boatAt = "east" THEN "west" ELSE "east")
           newPeople == [people EXCEPT ![boatAt] = @ \ g, ![dest] = @ \cup g]
       IN /\ \A b \in Banks : BankOK(newPeople[b])
          /\ boatAt' = dest
          /\ people' = newPeople

Next ==
    \/ \E g \in (SUBSET (Missionaries \cup Cannibals)) : MoveGroup(g)

Solution ==
    \/ \A b \in Banks : BankOK(b)
    /\ boatAt \in Banks
    /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Spec == Init /\ [][Next]_vars

====