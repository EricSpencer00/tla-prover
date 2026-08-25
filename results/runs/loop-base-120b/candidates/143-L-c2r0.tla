---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

CONSTANTS Missionaries, Cannibals

VARIABLES BoatAt, East, West

\* The set of all people
People == Missionaries \cup Cannibals

\* Type invariant
TypeOK ==
    /\ BoatAt \in {"East", "West"}
    /\ East \subseteq People
    /\ West \subseteq People
    /\ East \cup West = People
    /\ East \cap West = {}

\* A bank is safe when either it has no missionaries or
\* the number of cannibals does not exceed the number of missionaries.
Safe(bank) ==
    LET m == Missionaries \cap bank
        c == Cannibals \cap bank
    IN
        \/ m = {}
        \/ Cardinality(c) <= Cardinality(m)

\* Convenience definitions for the bank where the boat currently is
CurrentBank ==
    IF BoatAt = "East" THEN East ELSE West

OppositeBank ==
    IF BoatAt = "East" THEN West ELSE East

\* One crossing of the boat carrying one or two people.
Move ==
    \E S \subseteq CurrentBank :
        /\ Cardinality(S) \in 1..2
        /\ LET newCurrent == CurrentBank \ S
               newOpposite == OppositeBank \cup S
           IN
               /\ BoatAt' = IF BoatAt = "East" THEN "West" ELSE "East"
               /\ IF BoatAt = "East"
                      THEN /\ East' = newCurrent
                           /\ West' = newOpposite
                      ELSE /\ West' = newCurrent
                           /\ East' = newOpposite
               /\ Safe(East') /\ Safe(West')

\* The next-state relation
Next == Move

\* Initial state: everybody on the east bank, boat at east
Init ==
    /\ BoatAt = "East"
    /\ East = People
    /\ West = {}

\* Invariant used to obtain a solution trace:
\* it requires the east bank to stay non‑empty; a violation (east empty) is the solution.
Solution == East #= {}

\* (Optional) full specification
Spec == Init /\ [][Next]_<<BoatAt, East, West>>

====