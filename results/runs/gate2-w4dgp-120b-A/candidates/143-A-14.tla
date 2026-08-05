---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES bank, boatAt

vars == <<bank, boatAt>>

Group == Missionaries \cup Cannibals
Pairs == {x \cup y : x, y \in Group, x # y}

RECURSIVE Count(_)
Count(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE
                  IN 1 + Count(S \ {x})

TypeOK ==
  /\ bank \in [Banks -> Group]
  /\ boatAt \in Banks

Init ==
  /\ bank = [b \in Banks |-> IF b = "east" THEN Group ELSE {}]
  /\ boatAt = "east"

Move ==
  \/ \E p \in Group :
       /\ p \in bank[boatAt]
       /\ bank' = [bank EXCEPT ![boatAt] = @ \ {p}, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \cup {p}]
       /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
  \/ \E p \in Pairs :
       /\ p \subseteq bank[boatAt]
       /\ bank' = [bank EXCEPT ![boatAt] = @ \ p, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \cup p]
       /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

AtLeastOneMissionary(b) ==
  \E m \in Missionaries : m \in bank[b]

Unsafe(b) ==
  AtLeastOneMissionary(b) /\ (Count(bank[b] \cap Cannibals) > Count(bank[b] \cap Missionaries))

Next == Move

Solution ==
  /\ TypeOK
  /\ \A b \in Banks : ~Unsafe(b)
  /\ boatAt \in Banks

Spec == Init /\ [][Next]_vars

====