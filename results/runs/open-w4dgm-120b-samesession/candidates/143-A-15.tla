---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, people

vars == <<boatAt, people>>

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumOf(f, S \ {x})

OnBank(b, g) == Cardinality({p \in g : people[p] = b})

TypeOK ==
  /\ boatAt \in Banks
  /\ people \in [Missionaries \cup Cannibals -> Banks]

Init ==
  /\ boatAt = "east"
  /\ people = [p \in Missionaries \cup Cannibals |-> "east"]

Move ==
  /\ \E g \in SUBSET (Missionaries \cup Cannibals) :
       /\ g # {}
       /\ Cardinality(g) <= 2
       /\ \A p \in g : people[p] = boatAt
       /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east" IN
            /\ people' = [p \in Missionaries \cup Cannibals |-> IF p \in g THEN dest ELSE people[p]]
            /\ boatAt' = dest
  /\ \A b \in Banks :
       OnBank(b, Missionaries) # 0 => OnBank(b, Cannibals) <= OnBank(b, Missionaries)

Solution ==
  /\ \A b \in Banks :
       OnBank(b, Missionaries) # 0 => OnBank(b, Cannibals) <= OnBank(b, Missionaries)
  /\ \A b \in Banks : OnBank(b, Missionaries) + OnBank(b, Cannibals) >= 1

Next == Move

Spec == Init /\ [][Next]_vars

====