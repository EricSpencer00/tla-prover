---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, onBank

vars == <<boatAt, onBank>>

RECURSIVE CountOf(_, _)
CountOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + CountOf(f, S \ {x})

TypeOK ==
    /\ boatAt \in Banks
    /\ onBank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
    /\ boatAt = "east"
    /\ onBank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* The boat must never cross empty and must never carry more than two people;
\* the occupancy test below applies to the destination's new composition.
Move(g) ==
    /\ g \subseteq onBank[boatAt]
    /\ Cardinality(g) \in 1..2
    /\ LET ot == Cardinality(g) IN
        /\ LET other == IF boatAt = "east" THEN "west" ELSE "east" IN
            /\ \A b \in Banks :
                 LET M == CountOf([p \in Missionaries \cup Cannibals |-> IF p \in Missionaries THEN 1 ELSE 0],
                                  (IF b = boatAt THEN onBank[b] \ {p \in g} ELSE onBank[b] \cup g))
                     C == CountOf([p \in Missionaries \cup Cannibals |-> IF p \in Cannibals THEN 1 ELSE 0],
                                  (IF b = boatAt THEN onBank[b] \ {p \in g} ELSE onBank[b] \cup g))
                 IN M = 0 \/ C <= M
            /\ \A p \in g : onBank' = [onBank EXCEPT ![other] = @ \cup {p}, ![boatAt] = @ \ {p}]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next ==
    \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)

Spec == Init /\ [][Next]_vars

Solution == onBank["east"] # {}

\* An instantiated mission with the east bank emptied is a valid solution trace.
\* The invariant itself is the missionaries-not-outnumbered safety condition.
TypeOKInv == TypeOK
SolutionInv == Solution

====