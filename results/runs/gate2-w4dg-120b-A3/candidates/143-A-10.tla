---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES boatAt, bankPeople, boatLoad

vars == <<boatAt, bankPeople, boatLoad>>

Init ==
    /\ boatAt = "east"
    /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ boatLoad = {}

TypeOK ==
    /\ boatAt \in Banks
    /\ bankPeople \in [Banks -> SUBSET People]
    /\ boatLoad \subseteq People

\* A bank is safe if it has no missionaries, or cannibals are not outnumbering them
BankSafe(b) ==
    LET ms == Cardinality(bankPeople[b] \cap Missionaries)
        cs == Cardinality(bankPeople[b] \cap Cannibals)
    IN (ms = 0) \/ (cs <= ms)

\* The puzzle is solved when the east bank is empty
Solved == bankPeople["east"] = {}

Board ==
    { p \in bankPeople[boatAt] : Cardinality({q \in bankPeople[boatAt] : q <= p}) = 1 }

Move ==
    /\ \E g \in Board :
         /\ Cardinality(g) \in {1, 2}
         /\ bankPeople' = [bankPeople EXCEPT ![boatAt] = bankPeople[boatAt] \ g, ![IF boatAt = "east" THEN "west" ELSE "east"] = bankPeople[IF boatAt = "east" THEN "west" ELSE "east"] \cup g]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
    /\ boatLoad' = g
    /\ UNCHANGED <<boardPeople>>

Next == Move

Spec == Init /\ [][Next]_vars

\* Every bank, whenever it has missionaries, must not have more cannibals than missionaries
Solution == BankSafe("east") /\ BankSafe("west")

====