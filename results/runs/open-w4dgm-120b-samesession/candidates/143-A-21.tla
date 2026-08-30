---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES bank, boatAt, bankPeople

vars == <<bank, boatAt, bankPeople>>

RECURSIVE Total(_)
Total(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN bank[x] + Total(S \ {x})

TypeOK ==
    /\ bank \in [People -> Banks]
    /\ boatAt \in Banks
    /\ bankPeople \in [Banks -> SUBSET People]

Init ==
    /\ bank = [p \in People |-> "east"]
    /\ boatAt = "east"
    /\ bankPeople = [b \in Banks |-> {p \in People : "east" = b}]

Move(S) ==
    /\ S \subseteq bankPeople[boatAt]
    /\ Cardinality(S) \in {1, 2}
    /\ LET newBank == IF boatAt = "east" THEN "west" ELSE "east" IN
        /\ \A p \in People : bank' = [bank EXCEPT ![p] = IF p \in S THEN newBank ELSE bank[p]]
        /\ boatAt' = newBank
        /\ bankPeople' = [bankPeople EXCEPT ![boatAt] = bankPeople[boatAt] \ S, ![newBank] = bankPeople[newBank] \cup S]

Next == \E S \subseteq People : Move(S)

Solution == \A b \in Banks : Cardinality(bankPeople[b]) <= 2

SafeBanks ==
    \A b \in Banks :
        \/ bankPeople[b] \cap Missionaries = {}
        \/ Cardinality(bankPeople[b] \cap Cannibals) <= Cardinality(bankPeople[b] \cap Missionaries)

TypeOKInv == TypeOK

Spec == Init /\ [][Next]_vars

====