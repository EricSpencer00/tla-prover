---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
BoatCaps == 1..2

RECURSIVE SumSet(_)
SumSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN x + SumSet(S \ {x})

VARIABLES boatAt, bankPeople

vars == <<boatAt, bankPeople>>

TypeOK ==
    /\ boatAt \in Banks
    /\ bankPeople \in [Banks -> SUBSET People]

Init ==
    /\ boatAt = "east"
    /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank is safe if it holds no missionaries (only cannibals remain, which is
\* harmless) or its cannibals do not outnumber its missionaries.
SafeBank(b) ==
    LET P == bankPeople[b] IN
    LET ms == Cardinality(P \cap Missionaries) IN
    LET cs == Cardinality(P \cap Cannibals) IN
        \/ ms = 0
        \/ cs <= ms

Safe ==
    /\ SafeBank("east")
    /\ SafeBank("west")

\* The boat carries a group of size 1..2 and drops them on the far bank in one
\* step; the move is only always available when it leaves both banks safe.
Move ==
    /\ \E g \in SUBSET People :
         /\ g \subseteq bankPeople[boatAt]
         /\ Cardinality(g) \in BoatCaps
         /\ bankPeople' = [bankPeople EXCEPT ![boatAt] = @ \ g, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \cup g]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next == Move

Spec == Init /\ [][Next]_vars

\* The solution condition is that the east bank is never left empty; when a model
\* checker finds a trace that reaches an empty east bank, it has produced a
\* crossing solution, so a violation of this invariant is exactly what we are
\* after.
Solution == Cardinality(bankPeople["east"]) > 0

====