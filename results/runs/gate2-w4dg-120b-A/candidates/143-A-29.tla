---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
Groups == {s \in SUBSET People : s # {} /\ Cardinality(s) <= 2}

VARIABLES bank, distribution

vars == <<bank, distribution>>

RECURSIVE Ahigher(_)
Ahigher(b) ==
  IF b = 0 THEN 0
  ELSE IF b = 1 THEN 1
  ELSE 3

RECURSIVE CountP(_)
CountP(p) ==
  IF p = {} THEN 0
  ELSE LET x == CHOOSE y \in p : TRUE IN Ahigher(x) + CountP(p \ {x})

TypeOK ==
  /\ bank \in Banks
  /\ distribution \in [Banks -> SUBSET People]

Init ==
  /\ bank = "east"
  /\ distribution = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

MissionariesAt(b) == CountP(distribution[b] \cap Missionaries)
CannibalsAt(b)    == CountP(distribution[b] \cap Cannibals)

BankNotOutnumbered(b) ==
  \/ MissionariesAt(b) = 0
  \/ CannibalsAt(b) <= MissionariesAt(b)

Move ==
  /\ \E g \in Groups :
       /\ g \subseteq distribution[bank]
       /\ Cardinality(g) >= 1
       /\ Cardinality(g) <= 2
       /\ \E b2 \in Banks \ {bank} :
            /\ distribution' = [distribution EXCEPT ![bank] = @ \ g, ![b2] = @ \cup g]
            /\ bank' = b2
  /\ BankNotOutnumbered(bank)
  /\ BankNotOutnumbered("east")
  /\ BankNotOutnumbered("west")

Next == Move

Solution == bank = "west"

Spec == Init /\ [][Next]_vars

====