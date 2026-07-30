---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Bank == {"east", "west"}
People == Missionaries \cup Cannibals
PeoplePerBank == [east : [missionaries : 0..3, cannibals : 0..3], west : [missionaries : 0..3, cannibals : 0..3]]

RECURSIVE SumMissionaries(_)
SumMissionaries(S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE y \in S : TRUE IN x.missionaries + SumMissionaries(S \ {x})

RECURSIVE SumCannibals(_)
SumCannibals(S) == IF S = {} THEN 0
                    ELSE LET x == CHOOSE y \in S : TRUE IN x.cannibals + SumCannibals(S \ {x})

VARIABLES bank, distribution

vars == <<bank, distribution>>

TypeOK ==
    /\ bank \in Bank
    /\ distribution \in PeoplePerBank
    /\ distribution.east.missionaries + distribution.west.missionaries = Cardinality(Missionaries)
    /\ distribution.east.cannibals + distribution.west.cannibals = Cardinality(Cannibals)

Init ==
    /\ bank = "east"
    /\ distribution = [east |-> [missionaries |-> Cardinality(Missionaries), cannibals |-> Cardinality(Cannibals)],
                       west |-> [missionaries |-> 0, cannibals |-> 0]]

\* A crossing of one or two people, retaining safety on both banks.
Move ==
    \/ \E m \in 0..2, c \in 0..2 :
         /\ m + c >= 1 /\ m + c <= 2
         /\ bank = "east"
         /\ m <= distribution.east.missionaries
         /\ c <= distribution.east.cannibals
         /\ distribution.west.missionaries + m <= Cardinality(Missionaries)
         /\ distribution.west.cannibals + c <= Cardinality(Cannibals)
         /\ LET newDist ==
                [east |-> [missionaries |-> distribution.east.missionaries - m,
                           cannibals |-> distribution.east.cannibals - c],
                 west |-> [missionaries |-> distribution.west.missionaries + m,
                           cannibals |-> distribution.west.cannibals + c]]
            IN /\ (newDist.east.missionaries = 0 \/ newDist.east.cannibals <= newDist.east.missionaries)
               /\ (newDist.west.missionaries = 0 \/ newDist.west.cannibals <= newDist.west.missionaries)
               /\ distribution' = newDist
               /\ bank' = "west"
    \/ \E m \in 0..2, c \in 0..2 :
         /\ m + c >= 1 /\ m + c <= 2
         /\ bank = "west"
         /\ m <= distribution.west.missionaries
         /\ c <= distribution.west.cannibals
         /\ distribution.east.missionaries + m <= Cardinality(Missionaries)
         /\ distribution.east.cannibals + c <= Cardinality(Cannibals)
         /\ LET newDist ==
                [west |-> [missionaries |-> distribution.west.missionaries - m,
                           cannibals |-> distribution.west.cannibals - c],
                 east |-> [missionaries |-> distribution.east.missionaries + m,
                           cannibals |-> distribution.east.cannibals + c]]
            IN /\ (newDist.west.missionaries = 0 \/ newDist.west.cannibals <= newDist.west.missionaries)
               /\ (newDist.east.missionaries = 0 \/ newDist.east.cannibals <= newDist.east.missionaries)
               /\ distribution' = newDist
               /\ bank' = "east"

Next == Move

Spec == Init /\ [][Next]_vars

Solution == distribution.east.missionaries = 0

====