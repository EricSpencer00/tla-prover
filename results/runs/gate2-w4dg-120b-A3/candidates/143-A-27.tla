---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Missionaries,
    Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES
    boatAt,
    onBank

vars == <<boatAt, onBank>>

RECURSIVE Cardinality(_)
Cardinality(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Cardinality(S \ {x})

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET People]

BankCounts(b) ==
    <<Cardinality({p \in onBank[b] : p \in Missionaries}),
      Cardinality({p \in onBank[b] : p \in Cannibals})>>

BankSafe(b) ==
    LET c == BankCounts(b) IN c[2] = 0 \/ c[2] <= c[1]

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move ==
    /\ \E g \in SUBSET onBank[boatAt] :
        /\ g # {}
        /\ Cardinality(g) <= 2
        /\ LET newEast == IF boatAt = "east" THEN onBank["east"] \ g ELSE onBank["east"]
           newWest == IF boatAt = "east" THEN onBank["west"] \cup g ELSE onBank["west"] \ g
        IN /\ BankSafe("east")
           /\ BankSafe("west")
           /\ onBank' = [boatAt |-> IF boatAt = "east" THEN newEast ELSE newWest,
                         (IF boatAt = "east" THEN "west" ELSE "east") |-> IF boatAt = "east" THEN newWest ELSE newEast]
    /\ boatAt' = (IF boatAt = "east" THEN "west" ELSE "east")

Next ==
    \/ Move

Spec == Init /\ [][Next]_vars

Solution ==
    /\ BankSafe("east")
    /\ BankSafe("west")

====