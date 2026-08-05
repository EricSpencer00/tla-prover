---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatBank, peopleOnBank
vars == <<boatBank, peopleOnBank>>

RECURSIVE Count(_, _)
Count(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN (IF f[x] THEN 1 ELSE 0) + Count(f, S \ {x})

TypeOK ==
    /\ boatBank \in Banks
    /\ peopleOnBank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

OnBank(b, g) == { x \in Missionaries \cup Cannibals : peopleOnBank[b] = g }

\* A bank is safe if it has no missionaries or its cannibals never outnumber them.
BankSafe(b) ==
    \/ peopleOnBank[b] \cap Missionaries = {}
    \/ Count([x \in Missionaries \cup Cannibals |-> x \in Missionaries],
             peopleOnBank[b])
       >= Count([x \in Missionaries \cup Cannibals |-> x \in Cannibals],
               peopleOnBank[b])

\* The puzzle is solved when the east bank is empty (everyone reached the west bank).
Solved == peopleOnBank["east"] = {}

Init ==
    /\ boatBank = "east"
    /\ peopleOnBank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* Move: an embarkation group (1 or 2 people) on the current bank crosses to the
\* other bank, provided both banks stay safe -- cannibals never outnumber missionaries.
Move(g) ==
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ g \subseteq peopleOnBank[boatBank]
    /\ peopleOnBank[boatBank \ {g}]
    /\ peopleOnBank[IF boatBank = "east" THEN "west" ELSE "east" \cup g]
    /\ BankSafe(boatBank)
    /\ BankSafe(IF boatBank = "east" THEN "west" ELSE "east")
    /\ boatBank' = IF boatBank = "east" THEN "west" ELSE "east"
    /\ UNCHANGED <<Missionaries, Cannibals>>

Next == \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

\* The solution is a safety property so that a model checker that finds a violation
\* of 'east bank is non-empty' produces a concrete solution trace.
Solution == Solved

Spec == Init /\ [][Next]_vars

====