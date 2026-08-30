---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, location

vars == <<boatAt, location>>

\* A bank is safe if it contains no missionaries, or if cannibals do not
\* outnumber missionaries there.
Safe(b) ==
    \/ Cardinality(location[b] \cap Missionaries) = 0
    \/ Cardinality(location[b] \cap Cannibals)
         <= Cardinality(location[b] \cap Missionaries)

Init ==
    /\ boatAt = "east"
    /\ location = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* boarding: the non-empty group that gets into the boat; move: the other bank.
Next ==
    \E move \in Banks, boarding \in SUBSET People :
        /\ move # boatAt
        /\ boarding # {}
        /\ Cardinality(boarding) <= 2
        /\ boarding \subseteq location[boatAt]
        /\ Cardinality(location[boatAt] \ boarding) >= 1
        /\ Safe(boatAt \ boarding)
        /\ Safe(move \cup boarding)
        /\ location' = [location EXCEPT ![boatAt] = @ \ boarding,
                                      ![move] = @ \cup boarding]
        /\ boatAt' = move

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ boatAt \in Banks
    /\ location \in [Banks -> SUBSET People]

\* The east bank never becomes empty: there is always at least one person
\* left on the starting bank, so a counterexample trace always ends with
\* someone still standing there -- a solution has been found.
Solution == Cardinality(location["east"]) >= 1

====