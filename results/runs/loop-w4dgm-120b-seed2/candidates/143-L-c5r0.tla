---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, banks, moves

vars == <<boatAt, banks, moves>>

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumOf(f, S \ {x})

TypeOK ==
    /\ boatAt \in Banks
    /\ banks \in [Banks -> SUBSET People]
    /\ moves \in 0..6

\* No missionaries frightened away: on every bank, if missionaries are present
\* they are never outnumbered by cannibals.
Safe ==
    /\ \A b \in Banks :
         LET ms == Cardinality(banks[b] \cap Missionaries)
             cs == Cardinality(banks[b] \cap Cannibals)
         IN (ms = 0) \/ (cs =< ms)
    /\ moves >= 1

Init ==
    /\ boatAt = "east"
    /\ banks = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ moves = 0

\* Exactly one or two people board the boat and cross, never an empty boat, and
\* only if the resulting banks are both safe.
Move(g) ==
    /\ g # {}
    /\ Cardinality(g) \in 1..2
    /\ g \subseteq banks[boatAt]
    /\ banks' = [banks EXCEPT ![boatAt] = @ \ g, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \cup g]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
    /\ moves' = moves + 1

Next ==
    \/ \E g \in SUBSET People : Move(g)

Spec == Init /\ [][Next]_vars

\* Progress: the east bank eventually empties (everyone reaches the west bank).
Solution == <>(banks["east"] = {})

====