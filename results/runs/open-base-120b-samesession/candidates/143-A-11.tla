---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets, Naturals

\* ----------------------------------------------------------------------
\* Constants representing the sets of missionaries and cannibals.
\* The .cfg file must assign each of size three and disjoint.
\* ----------------------------------------------------------------------
CONSTANTS
    Missionaries,
    Cannibals

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Person == Missionaries \cup Cannibals
Banks   == {"East", "West"}

\* ----------------------------------------------------------------------
\* State variables
\*   boat   : the bank where the boat is currently docked
\*   People : a function mapping each bank to the set of persons located there
\* ----------------------------------------------------------------------
VARIABLES
    boat,
    People

\* ----------------------------------------------------------------------
\* Type correctness and safety (no missionaries outnumbered)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ boat \in Banks
    /\ People \in [Banks -> SUBSET Person]
    /\ \A b \in Banks :
          LET m == Cardinality(People[b] \cap Missionaries)
              c == Cardinality(People[b] \cap Cannibals)
          IN (m = 0) \/ (c <= m)

\* ----------------------------------------------------------------------
\* Initial state: everyone on the east bank, boat docked at east.
\* ----------------------------------------------------------------------
Init ==
    /\ boat = "East"
    /\ People = [b \in Banks |-> IF b = "East"
                                 THEN Missionaries \cup Cannibals
                                 ELSE {}]

\* ----------------------------------------------------------------------
\* Helper: the opposite bank of the current one.
\* ----------------------------------------------------------------------
Opposite(b) == IF b = "East" THEN "West" ELSE "East"

\* ----------------------------------------------------------------------
\* Move action: transport 1 or 2 persons from current bank to the other.
\* The move is only allowed when the resulting configuration satisfies TypeOK.
\* ----------------------------------------------------------------------
Move ==
    \E grp \subseteq People[boat] :
        /\ Cardinality(grp) \in {1, 2}
        /\ LET other == Opposite(boat) IN
           /\ People' = [People EXCEPT
                         ![boat] = People[boat] \ grp,
                         ![other] = People[other] \cup grp]
           /\ boat'   = other
           /\ TypeOK'

\* ----------------------------------------------------------------------
\* Next-state relation (including stuttering)
\* ----------------------------------------------------------------------
Next == Move \/ UNCHANGED << boat, People >>

\* ----------------------------------------------------------------------
\* Invariant that the east bank is non‑empty.
\* Violation of this invariant (east bank empty) signals a solution.
\* ----------------------------------------------------------------------
Solution == People["East"] # {}

====