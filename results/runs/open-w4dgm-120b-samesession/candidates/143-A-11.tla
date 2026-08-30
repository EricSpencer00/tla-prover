---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, people

vars == <<boatAt, people>>

TypeOK ==
    /\ boatAt \in Banks
    /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
    /\ boatAt = "east"
    /\ people = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

GroupBound == 2
MoveGroup == UNION { [k \in 1..GroupBound |-> {g[i] : i \in 1..k}] :
                      g \in [1..GroupBound -> SUBSET (Missionaries \cup Cannibals)] }

\* Safety: a bank with missionaries must not have more cannibals than missionaries.
\* A bank with only cannibals is safe by definition (no missionaries to endanger).
Safety ==
    /\ \A b \in Banks :
         LET mc == Cardinality(people[b] \cap Missionaries) IN
         LET cc == Cardinality(people[b] \cap Cannibals) IN
         mc = 0 \/ cc <= mc
    /\ MoveGroup \subseteq Missionaries \cup Cannibals

Move ==
    /\ \E g \in MoveGroup :
         /\ g \subseteq people[boatAt]
         /\ Cardinality(g) >= 1
         /\ people' = [people EXCEPT ![boatAt] = @ \ g, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \cup g]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next == Move

Spec == Init /\ [][Next]_vars

TypeOKInv == TypeOK

\* The puzzle is solved when the east bank is empty; the invariant holds
\* throughout the search and a counterexample to it is a solution trace.
Solution == people["east"] = {}

====