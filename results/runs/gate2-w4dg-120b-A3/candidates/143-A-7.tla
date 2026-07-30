---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Bank == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES bank, distribution
vars == <<bank, distribution>>

TypeOK ==
    /\ bank \in Bank
    /\ distribution \in [Bank -> SUBSET People]

Init ==
    /\ bank = "east"
    /\ distribution = [b \in Bank |-> IF b = "east" THEN People ELSE {}]

\* A bank is safe when either it holds no missionaries, or its cannibals do not
\* outnumber its missionaries; a bank of cannibals alone is trivially safe.
BankIsSafe(b) ==
    LET M == {p \in distribution[b] : p \in Missionaries}
        C == {p \in distribution[b] : p \in Cannibals}
    IN \/ M = {}
       \/ Cardinality(C) <= Cardinality(M)

\* The move action always moves people, and only when it keeps both banks safe.
Move(g) ==
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ g \subseteq distribution[bank]
    /\ LET other == IF bank = "east" THEN "west" ELSE "east"
           newDist == [distribution EXCEPT ![bank] = distribution[bank] \ g, ![other] = distribution[other] \cup g]
       IN /\ BankIsSafe(other)
          /\ BankIsSafe(bank)
          /\ distribution' = newDist
          /\ bank' = other

Next == \E g \in SUBSET People : Move(g)

\* The river is completely crossed when the east bank is empty.
Solution == distribution["east"] = {}

Spec == Init /\ [][Next]_vars

====