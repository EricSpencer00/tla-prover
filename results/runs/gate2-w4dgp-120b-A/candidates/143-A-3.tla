---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

Missionaries == {1, 2, 3}
Cannibals == {1, 2, 3}
People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES boatBank, bankPeople

TypeOK ==
  /\ boatBank \in Banks
  /\ bankPeople \in [Banks -> SUBSET People]

Init ==
  /\ boatBank = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move ==
  /\ \E grp \in SUBSET People :
       /\ grp # {}
       /\ Cardinality(grp) <= 2
       /\ grp \subseteq bankPeople[boatBank]
       /\ bankPeople' = [bankPeople EXCEPT ![boatBank] = @ \ grp, ![IF boatBank = "east" THEN "west" ELSE "east"] = @ \cup grp]
  /\ boatBank' = IF boatBank = "east" THEN "west" ELSE "east"

Next == Move

Solution ==
  /\ \A b \in Banks : (\E m \in Missionaries : m \in bankPeople[b]) => Cardinality({c \in Cannibals : c \in bankPeople[b]}) <= Cardinality({m \in Missionaries : m \in bankPeople[b]})
  /\ \A b \in Banks : Cardinality({c \in Cannibals : c \in bankPeople[b]}) <= 3
  /\ bankPeople["east"] # {}

====