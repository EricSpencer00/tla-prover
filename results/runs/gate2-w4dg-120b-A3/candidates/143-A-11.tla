---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

EastBank == "east"
WestBank == "west"
Banks == {EastBank, WestBank}

VARIABLES boatAt, onBank

Vars == <<boatAt, onBank>>

TypeOK ==
  /\ boatAt \in Banks
  /\ onBank \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = EastBank
  /\ onBank = [b \in Banks |-> IF b = EastBank THEN People ELSE {}]

\* On a bank, safety means either no missionaries, or missionaries not outnumbered.
BankSafe(b) ==
  \A g \in Missionaries :
    g \in onBank[b] => Cardinality(onBank[b] \cap Cannibals) <= Cardinality(onBank[b] \cap Missionaries)

Move(g1, g2) ==
  /\ g1 \in onBank[boatAt]
  /\ g2 \in onBank[boatAt]
  /\ Cardinality({g1, g2}) \in {1, 2}
  /\ boatAt' = IF boatAt = EastBank THEN WestBank ELSE EastBank
  /\ onBank' = [onBank EXCEPT ![boatAt] = onBank[boatAt] \ {g1, g2}, ![boatAt'] = onBank[boatAt'] \cup {g1, g2}]
  /\ BankSafe(boatAt)
  /\ BankSafe(boatAt')
  /\ Cardinality(onBank[boatAt] \ {g1, g2}) >= Cardinality(onBank[boatAt] \ {g1, g2} \cap Missionaries)
  /\ Cardinality(onBank[boatAt] \ {g1, g2}) >= Cardinality(onBank[boatAt] \ {g1, g2} \cap Cannibals)

Next == \E g1 \in People, g2 \in People : Move(g1, g2)

Solution == \A b \in Banks : BankSafe(b)

Spec == Init /\ [][Next]_Vars

====