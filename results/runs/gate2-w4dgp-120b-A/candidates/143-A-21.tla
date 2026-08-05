---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Missionaries \cap Cannibals = {}
ASSUME Missionaries \cup Cannibals # {}

Banks == {"east", "west"}

VARIABLES boatBank, bankPeople

vars == <<boatBank, bankPeople>>

RECURSIVE CountSubset(_)
CountSubset(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN (IF x \in Missionaries THEN 1 ELSE 0) + CountSubset(S \ {x})

RECURSIVE CountSet(_)
CountSet(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE IN (IF x \in Cannibals THEN 1 ELSE 0) + CountSet(S \ {x})

BankMeta(people) ==
    LET m == {p \in people : p \in Missionaries}
        c == {p \in people : p \in Cannibals}
    IN IF m = {} THEN TRUE ELSE CountSet(c) <= CountSubset(m)

TypeOK ==
    /\ boatBank \in Banks
    /\ bankPeople \in [Banks -> SUBSET Missionaries \cup Cannibals]

Init ==
    /\ boatBank = "east"
    /\ bankPeople = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

Move ==
    /\ \E g \in [Banks -> SUBSET Missionaries \cup Cannibals] :
        /\ Cardinality(g) \in 1..2
        /\ g \subseteq bankPeople[boatBank]
        /\ LET otherBank == IF boatBank = "east" THEN "west" ELSE "east" IN
            /\ bankPeople' = [bankPeople EXCEPT ![boatBank] = @ \ g, ![otherBank] = @ \cup g]
            /\ boatBank' = otherBank
    /\ BankMeta(bankPeople["east"])
    /\ BankMeta(bankPeople["west"])

Next == Move

(* Safe on both banks: missionaries are never outnumbered by cannibals; boat trips are
   never empty or overloaded; and at least one missionary has finally crossed. *)
Solution ==
    /\ \A b \in Banks : BankMeta(bankPeople[b])
    /\ boatBank \in Banks
    /\ Missionaries \cup Cannibals = Missionaries \cup Cannibals
    /\ bankPeople["west"] # {}

Spec == Init /\ [][Next]_vars

====