---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Bank == {"east", "west"}

VARIABLES dock, banks

vars == <<dock, banks>>

People == Missionaries \cup Cannibals

TypeOK ==
    /\ dock \in Bank
    /\ banks \in [Bank -> SUBSET People]

Init ==
    /\ dock = "east"
    /\ banks = [b \in Bank |-> IF b = "east" THEN People ELSE {}]

\* The boat never travels empty, and a move is only made if it leaves both banks
\* safe (no missionaries outnumbered on a bank where they are present).
Safe(b) ==
    LET M == Cardinality(banks[b] \cap Missionaries)
        C == Cardinality(banks[b] \cap Cannibals)
    IN \/ M = 0
       \/ C <= M

Next ==
    \/ \E g \in SUBSET People :
         /\ g # {}
         /\ Cardinality(g) <= 2
         /\ g \subseteq banks[dock]
         /\ LET b2 == IF dock = "east" THEN "west" ELSE "east" IN
            /\ banks' = [banks EXCEPT ![dock] = @ \ g, ![b2] = @ \cup g]
            /\ dock' = b2
         /\ Safe("east") /\ Safe("west")

Spec == Init /\ [][Next]_vars

Solution ==
    /\ TypeOK
    /\ banks["east"] = {}

====