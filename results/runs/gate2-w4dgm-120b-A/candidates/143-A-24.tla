---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, occupants, traversing

vars == <<boatAt, occupants, traversing>>

\* Safety bookkeeping: a bank is safe if it contains no missionaries at all
\* or its cannibals never outnumber its missionaries.
\* traversing records the two people currently aboard the boat (empty set = none).
TypeOK ==
    /\ boatAt \in Banks
    /\ occupants \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
    /\ traversing \subseteq (Missionaries \cup Cannibals)

Init ==
    /\ boatAt = "east"
    /\ occupants = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]
    /\ traversing = {}

\* A crossing only executes when the resulting occupancy on both banks would
\* remain safe; the boat always carries at least one and at most two people.
Move ==
    /\ traversing = {}
    /\ \E g \in SUBSET (Missionaries \cup Cannibals) :
         /\ Cardinality(g) \in 1..2
         /\ g \subseteq occupants[boatAt]
         /\ \A b \in Banks :
              LET newOcc == [occupants EXCEPT ![b] = IF b = boatAt THEN occupants[b] \ g
                                                            ELSE IF b = (IF boatAt = "east" THEN "west" ELSE "east") THEN occupants[b] \cup g
                                                            ELSE occupants[b]]
                  safe == (Missionaries \cap newOcc = {}) \/ (Cardinality(Cannibals \cap newOcc) <= Cardinality(Missionaries \cap newOcc))
              IN safe
    /\ traversing' = g
    /\ occupants' = [occupants EXCEPT ![boatAt] = occupants[boatAt] \ g]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Deliver ==
    /\ traversing # {}
    /\ occupants' = [occupants EXCEPT ![boatAt] = occupants[boatAt] \cup traversing]
    /\ traversing' = {}
    /\ UNCHANGED boatAt

Next == Move \/ Deliver

\* The puzzle's true success condition: everyone has reached the far bank.
Solution == occupants["east"] = {}

\* The invariant the model checker hunts: no bank ever has missionaries outnumbered.
TypeOKInv == \A b \in Banks : (Missionaries \cap occupants[b] = {}) \/ (Cardinality(Cannibals \cap occupants[b]) <= Cardinality(Missionaries \cap occupants[b]))

Spec == Init /\ [][Next]_vars

====