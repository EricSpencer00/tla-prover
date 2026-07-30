---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES boatAt, bankPeople

vars == <<boatAt, bankPeople>>

TypeOK ==
  /\ boatAt \in Banks
  /\ bankPeople \in [Banks -> SUBSET People]

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(b) ==
  LET ms == Missionaries \cap bankPeople[b]
      cs == Cannibals \cap bankPeople[b]
  IN \/ ms = {}
     \/ Cardinality(cs) <= Cardinality(ms)

\* The boat must always carry one or two people per crossing.
BoatLoadValid ==
  /\ Cardinality(Missionaries \cup Cannibals) = 6
  /\ Cardinality(Missionaries) = 3
  /\ Cardinality(Cannibals) = 3

Init ==
  /\ boatAt = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A group of one or two people boards the boat on the current bank and crosses.
Move ==
  /\ \E g \in SUBSET People :
       /\ g # {}
       /\ Cardinality(g) <= 2
       /\ g \subseteq bankPeople[boatAt]
       /\ LET other == IF boatAt = "east" THEN "west" ELSE "east"
          IN /\ bankPeople' = [bankPeople EXCEPT ![boatAt] = @ \ g, ![other] = @ \cup g]
             /\ boatAt' = other
  /\ UNCHANGED <<>>

Next == Move

Spec == Init /\ [][Next]_vars

\* No missionaries are ever outnumbered by cannibals on either bank.
Solution == \A b \in Banks : BankSafe(b)

====