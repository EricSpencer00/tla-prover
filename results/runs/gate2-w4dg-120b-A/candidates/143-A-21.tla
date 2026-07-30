---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Missionaries, Cannibals

People == Missionaries \cup Cannibals

Banks == {"east", "west"}

VARIABLES
    boat, bankPeople

vars == <<boat, bankPeople>>

RECURSIVE MembersOf(_)
MembersOf(S) == IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE
                     IN 1 + MembersOf(S \ {x})

BankUnsafe(b) ==
    LET m == MembersOf(bankPeople[b] \cap Missionaries)
        c == MembersOf(bankPeople[b] \cap Cannibals)
    IN (m # 0) /\ (c > m)

TypeOK ==
    /\ boat \in Banks
    /\ bankPeople \in [Banks -> SUBSET People]

Init ==
    /\ boat = "east"
    /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move(people) ==
    /\ people \subseteq bankPeople[boat]
    /\ Cardinality(people) \in {1, 2}
    /\ ~BankUnsafe(boat)
    /\ LET other == IF boat = "east" THEN "west" ELSE "east"
           newBank == [bankPeople[boat] \ {x \in people} EXCEPT ![boat] = (bankPeople[boat]) \ {x \in people}]
       IN /\ ~BankUnsafe(other)
          /\ bankPeople' = [bankPeople EXCEPT ![boat] = newBank[boat], ![other] = newBank[other]]
    /\ boat' = IF boat = "east" THEN "west" ELSE "east"

Next == \E people \in SUBSET People : Move(people)

Spec == Init /\ [][Next]_vars

Solution == \A b \in Banks : ~BankUnsafe(b)

====