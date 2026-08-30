---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
BoatCap == 2
NoBoard == 0

VARIABLES boat, distribution, board, startBank

vars == <<boat, distribution, board, startBank>>

TypeOK ==
    /\ boat \in Banks
    /\ distribution \in [Banks -> SUBSET People]
    /\ board \in SUBSET People
    /\ startBank \in Banks
    /\ Cardinality(board) <= BoatCap

Init ==
    /\ boat = "east"
    /\ distribution = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ board = {}
    /\ startBank = "east"

BoardSet ==
    { S \in SUBSET Missionaries : 1 <= Cardinality(S) /\ Cardinality(S) <= BoatCap }
        \cup
    { S \in SUBSET Cannibals : 1 <= Cardinality(S) /\ Cardinality(S) <= BoatCap }
        \cup
    { S \in SUBSET People :
        /\ S # {}
        /\ S \subseteq Missionaries \cup Cannibals
        /\ Cardinality(S) >= 1 /\ Cardinality(S) <= BoatCap }

\* Safety is checked for both banks as a whole as part of each move, so a
\* one-bank view is enough to decide if the move is allowed.
SafeAfterMove(S, src) ==
    /\ S \subseteq distribution[src]
    /\ Cardinality(S) >= 1 /\ Cardinality(S) <= BoatCap
    /\ LET left == Cardinality(src \cap Missionaries)
           right == Cardinality(src \cap Cannibals)
           srcMissionaries == left
           srcCannibals == right
           dstMissionaries == Cardinality((IF src = "east" THEN "west" ELSE "east") \cap Missionaries)
           dstCannibals == Cardinality((IF src = "east" THEN "west" ELSE "east") \cap Cannibals)
           Smission == Cardinality(S \cap Missionaries)
           Scannibals == Cardinality(S \cap Cannibals)
       IN
           /\ (srcMissionaries = 0 \/ (srcMissionaries - Smission) >= (srcCannibals - Scannibals))
           /\ (dstMissionaries = 0 \/ (dstMissionaries + Smission) >= (dstCannibals + Scannibals))

\* The boat is always carrying as many people as it boarded with, and never
\* carries no one -- that is what makes the crossing non-empty.
Move ==
    \E S \in BoardSet :
        \E src \in Banks :
            /\ SafeAfterMove(S, src)
            /\ board' = S
            /\ startBank' = src
            /\ boat' = IF src = "east" THEN "west" ELSE "east"
            /\ distribution' = [distribution EXCEPT ![src] = @ \ S, ![boat] = @ \cup S]

Next == Move

\* Transporting everybody to the far bank is the only way to falsify this.
Solution == \A b \in Banks : b # "east" => distribution[b] = People

\* No missionaries outnumbered by cannibals on either bank; the boat never
\* travels empty or over its passenger limit.
TypeOKInv ==
    /\ TypeOK
    /\ Solution
    /\ board # {}
    /\ Cardinality(board) <= BoatCap

Spec == Init /\ [][Next]_vars

====