---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boat, bank
vars == <<boat, bank>>

BankPairs == [east |-> east, west |-> west]

Boats == {1, 2}

People == Missionaries \cup Cannibals

RECURSIVE Tally(_, _)
Tally(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Tally(f, S \ {x})

CurrentBank == IF boat = "east" THEN "east" ELSE "west"
OtherBank == IF boat = "east" THEN "west" ELSE "east"

TypeOK ==
  /\ boat \in {"east", "west"}
  /\ bank \in [BankPairs -> SUBSET People]
  /\ \A g \in BankPairs : Cardinality(bank[g] \cap Missionaries) <= 3
  /\ \A g \in BankPairs : Cardinality(bank[g] \cap Cannibals) <= 3

Init ==
  /\ boat = "east"
  /\ bank = [BankPairs |-> IF #BankPairs = 2 THEN (IF #BankPairs[1] = 2 THEN {} ELSE Missionaries \cup Cannibals) ELSE {}]

Move ==
  /\ \E g \in People, h \in People :
       /\ g \in bank[CurrentBank]
       /\ h \in bank[CurrentBank]
       /\ g # h
       /\ Cardinality(bank[CurrentBank]) - 2 >= 1
       /\ Cardinality(bank[OtherBank]) + 2 <= 3
       /\ bank' = [bank EXCEPT ![CurrentBank] = @ \ {g, h}, ![OtherBank] = @ \cup {g, h}]
  \/ \E g \in People :
       /\ g \in bank[CurrentBank]
       /\ Cardinality(bank[CurrentBank]) - 1 >= 1
       /\ Cardinality(bank[OtherBank]) + 1 <= 3
       /\ bank' = [bank EXCEPT ![CurrentBank] = @ \ {g}, ![OtherBank] = @ \cup {g}]
  /\ boat' = OtherBank

Next == Move

Specification == Init /\ [][Next]_vars

Solution ==
  /\ TypeOK
  /\ Cardinality(bank["west"] \cap Missionaries) >= Cardinality(bank["west"] \cap Cannibals)
  /\ Cardinality(bank["east"] \cap Missionaries) >= Cardinality(bank["east"] \cap Cannibals)

====