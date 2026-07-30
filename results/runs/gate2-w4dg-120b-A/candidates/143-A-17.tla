---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS
    Missionaries, Cannibals

Banks == {"west", "east"}

VARIABLES
    boatBank
    bankPeople

vars == <<boatBank, bankPeople>>

People == Missionaries \cup Cannibals

RECURSIVE OnBank(_)
OnBank(b) ==
    IF b = 0 THEN {}
    ELSE LET x == CHOOSE y \in People : TRUE IN {x} \cup OnBank(b - 1)

RECURSIVE Count(_, _)
Count(b, S) ==
    IF b = 0 THEN 0
    ELSE LET x == CHOOSE y \in People : TRUE IN (IF x \in S THEN 1 ELSE 0) + Count(b - 1, S)

RECURSIVE Safeness(_)
Safeness(b) ==
    IF b = 0 THEN TRUE
    ELSE LET x == CHOOSE y \in People : TRUE IN
        LET remaining == Safeness(b - 1) IN
            IF x \in Missionaries THEN
                IF Count(b, Missionaries) = 0 THEN remaining
                ELSE remaining /\ Count(b, Cannibals) <= Count(b, Missionaries)
            ELSE remaining

TypeOK ==
    /\ boatBank \in Banks
    /\ bankPeople \in [Banks -> SUBSET People]
    /\ Cardinality(bankPeople["west"]) = Cardinality(bankPeople["east"])

\* A bank is safe if it has no missionaries, or its cannibals are not outnumbering them.
SafeBanks == Safeness(6)

Init ==
    /\ boatBank = "east"
    /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* Move a non-empty group of one or two people across; only allowed if each bank stays safe.
Move ==
    /\ Cardinality(bankPeople[boatBank]) >= 1
    /\ \E g \in [Missionaries \cup Cannibals -> BOOLEAN] :
         /\ Cardinality({x \in People : g[x]}) >= 1
         /\ Cardinality({x \in People : g[x]}) <= 2
         /\ bankPeople' = [bankPeople EXCEPT ![boatBank] = bankPeople[boatBank] \ {x \in People : g[x]}, !["west", "east"][boatBank] = bankPeople["west", "east"][boatBank] \cup {x \in People : g[x]}]
    /\ boatBank' = ["west", "east"][boatBank]
    /\ UNCHANGED <<>>

Next == Move

Spec == Init /\ [][Next]_vars

Solution == SafeBanks

====