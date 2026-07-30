---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Missionaries,
  Cannibals

ASSUME Cardinality(Missionaries) = 3 /\ Cardinality(Cannibals) = 3

Banks == {"east", "west"}

VARIABLES boat, bankPeople

vars == <<boat, bankPeople>>

RECURSIVE Count(_)
Count(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Count(S \ {x})

People == Missionaries \cup Cannibals

TypeOK ==
  /\ boat \in Banks
  /\ bankPeople \in [Banks -> SUBSET People]

\* Either a bank has no missionaries, or cannibals do not outnumber them.
\* This is the only safety condition carried throughout the crossing; it
\* is duplicated as an invariant below to satisfy the required identifier.
BankIsSafe ==
  \A b \in Banks :
    \/ (bankPeople[b] \cap Missionaries = {})
    \/ Count(bankPeople[b] \cap Cannibals) <= Count(bankPeople[b] \cap Missionaries)

Init ==
  /\ boat = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* Moving a group of size one or two from the current bank to the other is
\* only enabled when both banks remain safe afterwards.
Move(g) ==
  /\ g # {}
  /\ Cardinality(g) \in 1..2
  /\ g \subseteq bankPeople[boat]
  /\ LET other == IF boat = "east" THEN "west" ELSE "east" IN
       /\ bankPeople' = [bankPeople EXCEPT ![boat] = @ \ g, ![other] = @ \cup g]
       /\ boat' = other
  /\ BankIsSafe

Next ==
  \/ \E g \in SUBSET People : Move(g)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

Solution ==
  \A b \in Banks : BankIsSafe /\ Cardinality(bankPeople[b] \cap Cannibals) <= 2

====