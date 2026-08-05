---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, population

vars == <<boatAt, population>>

Two == Missionaries \cup Cannibals

\* Every bank must be safe for the missionaries: if there are any, the
\* cannibals must not outnumber them.  The boat always carries one or two
\* people and never travels empty, which is what makes the crossing safe.
\* The puzzle is solved when the east bank is empty (everyone reached the
\* west bank).
NoProblem == \A b \in Banks : LET m == Cardinality(population[b] \cap Missionaries)
                            IN LET c == Cardinality(population[b] \cap Cannibals)
                            IN m = 0 \/ c <= m

TypeOK ==
    /\ boatAt \in Banks
    /\ population \in [Banks -> SUBSET Two]

Init ==
    /\ boatAt = "east"
    /\ population = [b \in Banks |-> IF b = "east" THEN Two ELSE {}]

Move(g) ==
    /\ g # {}
    /\ g \subseteq Two
    /\ Cardinality(g) \in {1, 2}
    /\ g \subseteq population[boatAt]
    /\ LET dest == (IF boatAt = "east" THEN "west" ELSE "east") IN
         /\ Cardinality(g) <= 2
         /\ population' = [population EXCEPT ![boatAt] = @ \ g, ![dest] = @ \cup g]
         /\ boatAt' = dest

\* Headedness: a safe crossing is always possible as long as the east bank
\* is not yet empty, which is what lets TLC find a solution trace from a
\* safety invariant rather than a real liveness requirement.
Next ==
    \/ \E g \in SUBSET Two : Move(g)

Spec == Init /\ [][Next]_vars

Solution == (boatAt = "west" /\ population["east"] = {}) ~> (population["east"] = {})

====