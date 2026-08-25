---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

VARIABLES east, west, boat

\* --------------------------------------------------------------
\* Helper definitions
\* --------------------------------------------------------------

MissionariesOn(S) == { p \in S : p \in Missionaries }
CannibalsOn(S)    == { p \in S : p \in Cannibals }

\* A bank is safe iff it contains no missionaries or the number of
\* cannibals does not exceed the number of missionaries.
Safe(S) ==
    \/ MissionariesOn(S) = {}
    \/ Cardinality(CannibalsOn(S)) <= Cardinality(MissionariesOn(S))

\* --------------------------------------------------------------
\* Type correctness invariant
\* --------------------------------------------------------------
TypeOK ==
    /\ boat \in {"East", "West"}
    /\ east \subseteq Missionaries \cup Cannibals
    /\ west \subseteq Missionaries \cup Cannibals
    /\ east \cap west = {}
    /\ east \cup west = Missionaries \cup Cannibals

\* --------------------------------------------------------------
\* Initial state
\* --------------------------------------------------------------
Init ==
    /\ boat = "East"
    /\ east = Missionaries \cup Cannibals
    /\ west = {}
    /\ Safe(east)
    /\ Safe(west)

\* --------------------------------------------------------------
\* Moves
\* --------------------------------------------------------------
MoveEastToWest ==
    /\ boat = "East"
    /\ \E grp \subseteq east :
          /\ grp # {}
          /\ Cardinality(grp) \in 1..2
          /\ east' = east \ grp
          /\ west' = west \cup grp
          /\ boat' = "West"
          /\ Safe(east')
          /\ Safe(west')

MoveWestToEast ==
    /\ boat = "West"
    /\ \E grp \subseteq west :
          /\ grp # {}
          /\ Cardinality(grp) \in 1..2
          /\ west' = west \ grp
          /\ east' = east \cup grp
          /\ boat' = "East"
          /\ Safe(east')
          /\ Safe(west')

Next == MoveEastToWest \/ MoveWestToEast

\* --------------------------------------------------------------
\* Safety property that is *violated* when a solution is reached.
\* The model checker will look for a counterexample to this invariant,
\* i.e., a state where the east bank is empty.
\* --------------------------------------------------------------
Solution == east # {}

====