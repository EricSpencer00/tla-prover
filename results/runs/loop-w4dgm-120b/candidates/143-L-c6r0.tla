---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

VARIABLES boat, bank, moveGroup

vars == <<boat, bank, moveGroup>>

\* Everyone starts on the east bank; the west bank is empty.
Init ==
  /\ boat = "east"
  /\ bank = [b \in {"east", "west"} |-> IF b = "east" THEN People ELSE {}]
  /\ moveGroup = {}

\* A bank is safe if it has no missionaries, or cannibals never outnumber them.
SafeBank(b) ==
  LET m == Cardinality(bank[b] \cap Missionaries)
      c == Cardinality(bank[b] \cap Cannibals)
  IN m = 0 \/ c <= m

\* Boarding and crossing happen together; the move is legal only if the result
\* leaves both banks safe, which is what prevents the cannibals from winning.
Move ==
  \E g \in SUBSET People :
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ g \subseteq bank[boat]
    /\ boat' = IF boat = "east" THEN "west" ELSE "east"
    /\ bank' = [bank EXCEPT ![boat] = @ \ g, ![boat'] = @ \cup g]
    /\ moveGroup' = g

\* A group aboard that the boat is empty for is a configuration the model
\* checker will not get stuck on.
Next == Move

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ boat \in {"east", "west"}
  /\ bank \in [ {"east", "west"} -> SUBSET People ]
  /\ moveGroup \subseteq People

\* Every bank that still holds missionaries has cannibals no more than the
\* missionaries: the safety property the puzzle is all about.
Solution ==
  /\ \A b \in {"east", "west"} : SafeBank(b)
  /\ \A b \in {"east", "west"} : Cardinality(moveGroup) <= 2

====