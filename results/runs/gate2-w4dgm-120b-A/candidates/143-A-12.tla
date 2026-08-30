---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, onBank

vars == <<boatAt, onBank>>

People == Missionaries \cup Cannibals

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank with missionaries is safe only if cannibals do not outnumber them
\* (or there are no missionaries there at all).
BankIsSafe(b) ==
    LET mc == Cardinality(onBank[b] \cap Missionaries)
        cc == Cardinality(onBank[b] \cap Cannibals)
    IN (mc = 0) \/ (cc <= mc)

\* Boarding a non-empty group of size one or two and crossing to the other bank,
\* staying within the safety condition on both banks.
Move ==
    \E S \in SUBSET onBank[boatAt] :
        /\ Cardinality(S) \in 1..2
        /\ LET b2 == IF boatAt = "east" THEN "west" ELSE "east" IN
            /\ \A b \in Banks : Cardinality(onBank[b] \ S) <= Cardinality(onBank[b])
            /\ onBank' = [b \in Banks |-> IF b = boatAt THEN onBank[b] \ S
                                             ELSE IF b = (IF boatAt = "east" THEN "west" ELSE "east")
                                                THEN onBank[b] \cup S ELSE onBank[b]]
            /\ boatAt' = b2

Next == Move

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]

\* Every bank that has missionaries must not be outnumbered by cannibals.
Soln ==
    /\ \A b \in Banks : BankIsSafe(b)
    /\ \A b \in Banks : Cardinality(onBank[b]) <= 2

Spec == Init /\ [][Next]_vars

====