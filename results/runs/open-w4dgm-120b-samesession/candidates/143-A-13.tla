---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \union Cannibals

\* peopleAt[b] = who is currently on bank b; boatDocked = where the boat sits.
VARIABLES peopleAt, boatDocked

vars == <<peopleAt, boatDocked>>

\* Safety: a bank with missionaries must not have more cannibals than them.
BankSafe(b) == (peopleAt[b] \cap Missionaries = {}) \/ (Cardinality(peopleAt[b] \cap Cannibals)
                  <= Cardinality(peopleAt[b] \cap Missionaries))

TypeOK ==
    /\ peopleAt \in [Banks -> SUBSET People]
    /\ peopleAt["east"] \union peopleAt["west"] = People
    /\ peopleAt["east"] \intersect peopleAt["west"] = {}
    /\ boatDocked \in Banks

Init ==
    /\ peopleAt = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ boatDocked = "east"

\* Boarding and landing happen in one step; the boat never ends the move empty.
Move ==
    \E g \in (SUBSET peopleAt[boatDocked]) \cap (SUBSET People) :
        /\ g # {}
        /\ Cardinality(g) <= 2
        /\ peopleAt' = [peopleAt EXCEPT ![boatDocked] = @ \ g,
                                        ![IF boatDocked = "east" THEN "west" ELSE "east"] = @ \cup g]
        /\ boatDocked' = IF boatDocked = "east" THEN "west" ELSE "east"
        /\ BankSafe("east") /\ BankSafe("west")

Next == Move

Solution == \A b \in Banks : BankSafe(b)

\* The "river-crossing" liveness property is captured here as an invariant on the
\* east bank (the source) rather than as a separate LIVENESS clause, so a violation
\* is immediately visible to a model checker as a deadlock.
SolutionBound == peopleAt["east"] # {}

Spec == Init /\ [][Next]_vars
        /\ (\A a \in People : SF_vars(Move))
        /\ WF_vars(Next)

====