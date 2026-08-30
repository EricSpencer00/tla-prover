---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES dock, people

vars == <<dock, people>>

RECURSIVE SumF(_, _)
SumF(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumF(f, S \ {x})

\* A bank is safe if it contains no missionaries or its cannibals are not
\* outnumbered by them; that is the whole condition the crossing must preserve.
\* The boat never carries zero or more than two people, by construction of
\* the move action below.
BankSafe(b) ==
    \/ people[b][Missionaries] = 0
    \/ people[b][Cannibals] <= people[b][Missionaries]

TypeOK ==
    /\ dock \in Banks
    /\ people \in [Banks -> [Missionaries : 0..Cardinality(Missionaries),
                             Cannibals : 0..Cardinality(Cannibals)]]

Init ==
    /\ dock = "east"
    /\ people = [b \in Banks |-> [Missionaries |-> Cardinality(Missionaries),
                                   Cannibals |-> Cardinality(Cannibals)]]

Move ==
    \E m \in 0..Cardinality(Missionaries), c \in 0..Cardinality(Cannibals) :
        /\ m + c \in 1..2
        /\ m <= people[dock][Missionaries]
        /\ c <= people[dock][Cannibals]
        /\ LET dest == IF dock = "east" THEN "west" ELSE "east" IN
            /\ people' = [people EXCEPT ![dock] = [Missionaries |-> @[Missionaries] - m,
                                                   Cannibals |-> @[Cannibals] - c],
                          ![dest] = [Missionaries |-> @[Missionaries] + m,
                                     Cannibals |-> @[Cannibals] + c]]
        /\ dock' = dest

Next == Move

Solution == \A b \in Banks : BankSafe(b)

Spec == Init /\ [][Next]_vars

====