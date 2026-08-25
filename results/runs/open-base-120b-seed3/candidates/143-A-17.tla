---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Definitions of banks and boat location
\* ----------------------------------------------------------------------
East == "East"
West == "West"
Banks == {East, West}

VARIABLES boatAt, people

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ boatAt \in Banks
    /\ people \in [Missionaries \cup Cannibals -> Banks]

\* ----------------------------------------------------------------------
\* Helper definitions for safety checking
\* ----------------------------------------------------------------------
MissionariesOn(b) == { p \in Missionaries : people[p] = b }
CannibalsOn(b)   == { p \in Cannibals   : people[p] = b }

Safe(b) ==
    /\ (Cardinality(MissionariesOn(b)) = 0)
       \/ (Cardinality(CannibalsOn(b)) <= Cardinality(MissionariesOn(b)))

SafeAll ==
    /\ Safe(East)
    /\ Safe(West)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ boatAt = East
    /\ people = [p \in Missionaries \cup Cannibals |-> East]
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Move action: transport 1 or 2 people from current bank to the other bank
\* ----------------------------------------------------------------------
Move ==
    \E S \subseteq (Missionaries \cup Cannibals) :
        /\ Cardinality(S) \in 1..2
        /\ \A p \in S : people[p] = boatAt
        LET newBoat == IF boatAt = East THEN West ELSE East IN
            /\ boatAt' = newBoat
            /\ \A p \in (Missionaries \cup Cannibals) :
                  IF p \in S
                  THEN people'[p] = newBoat
                  ELSE people'[p] = people[p]
            /\ SafeAll'

Next == Move

\* ----------------------------------------------------------------------
\* Solution invariant (violated exactly when puzzle solved)
\* ----------------------------------------------------------------------
Solution ==
    \E p \in Missionaries \cup Cannibals : people[p] = East

\* ----------------------------------------------------------------------
\* Specification (not required by the cfg but useful for completeness)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<boatAt, people>>

====