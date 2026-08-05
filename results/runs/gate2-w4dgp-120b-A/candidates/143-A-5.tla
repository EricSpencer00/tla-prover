---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatAt, region

vars == <<boatAt, region>>

Banks == {"east", "west"}

Everyone == Missionaries \cup Cannibals

\* board(s) is the set of people on the departing bank who step into the boat;
\* it must be non-empty and never exceed the boat's capacity of two.
MoveSets == {s \in SUBSET Everyone : 1 <= Cardinality(s) /\ Cardinality(s) <= 2}

TypeOK ==
    /\ boatAt \in Banks
    /\ region \in [Banks -> SUBSET Everyone]

Init ==
    /\ boatAt = "east"
    /\ region = [b \in Banks |-> IF b = "east" THEN Everyone ELSE {}]

\* A crossing is permitted only when the resulting configuration on both banks
\* stays safe: wherever missionaries remain, they are not outnumbered by cannibals.
SafeAfterCrossing(s) ==
    /\ s \subseteq region[boatAt]
    /\ LET arrival == (IF boatAt = "east" THEN "west" ELSE "east") IN
        /\ (Cardinality(region["east"] \ s) = 0 \/ Cardinality((region["west"] \cup s) \cap Cannibals) <= Cardinality((region["west"] \cup s) \cap Missionaries))
        /\ (Cardinality(region["west"] \ s) = 0 \/ Cardinality((region["east"] \cup s) \cap Cannibals) <= Cardinality((region["east"] \cup s) \cap Missionaries))

Next ==
    \E s \in MoveSets :
        /\ SafeAfterCrossing(s)
        /\ LET arrival == (IF boatAt = "east" THEN "west" ELSE "east") IN
            /\ region' = [region EXCEPT ![boatAt] = @ \ s, ![arrival] = @ \cup s]
            /\ boatAt' = arrival

Next == Next

\* Progress is only claimed from a state where a move is still possible; when no
\* crossing remains enabled (all are safe and non-empty), the last move has been made.
NextEnabled == \E s \in MoveSets : SafeAfterCrossing(s)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Safety: missionaries are never outnumbered on any bank where they stand.
Solution ==
    /\ \A b \in Banks : region[b] \cap Missionaries = {} \/ Cardinality(region[b] \cap Cannibals) <= Cardinality(region[b] \cap Missionaries)
    /\ (cardinality(Missionaries) + cardinality(Cannibals) >= 2 /\ cardinality(Everyone) <= 6)

====