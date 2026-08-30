---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Missionaries # {} /\ Cannibals # {} /\ Missionaries \cap Cannibals = {}

Banks == {"east", "west"}
AllPeople == Missionaries \cup Cannibals
EastBankServants == Missionaries \cap Cannibals
MinCapacity == 1
MaxCapacity == 2

VARIABLES boatAt, people, previousMove

vars == <<boatAt, people, previousMove>>

\* Safety condition: a bank is safe if it has no missionaries (nothing to endanger)
\* or if the number of cannibals there does not exceed the number of missionaries.
IsBankSafe(b) ==
  LET np == Cardinality(people[b] \cap Missionaries)
      nc == Cardinality(people[b] \cap Cannibals)
  IN np = 0 \/ nc <= np

TypeOK ==
  /\ boatAt \in Banks
  /\ people \in [Banks -> SUBSET AllPeople]
  /\ previousMove \subseteq AllPeople

Init ==
  /\ boatAt = "east"
  /\ people = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]
  /\ previousMove = {}

\* One or two people board at the current bank and arrive at the other side,
\* and the move is only allowed if both banks stay safe afterwards.
Move ==
  \E g \in SUBSET AllPeople :
    /\ Cardinality(g) \in MinCapacity..MaxCapacity
    /\ g \subseteq people[boatAt]
    /\ LET otherBank == CHOOSE b \in Banks : b # boatAt
           newPeople == [bb \in Banks |-> IF bb = boatAt THEN people[bb] \ g ELSE IF bb = otherBank THEN people[bb] \cup g ELSE people[bb]]
       IN /\ IsBankSafe(otherBank)
          /\ IsBankSafe(boatAt)
          /\ people' = newPeople
    /\ boatAt' = CHOOSE b \in Banks : b # boatAt
    /\ previousMove' = g

Next == Move

Spec == Init /\ [][Next]_vars

Solution ==
  /\ \A b \in Banks : IsBankSafe(b)
  /\ people["east"] = {}

====