---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, bank, crossing

vars == <<boatAt, bank, crossing>>

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ crossing \in 0..2

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ crossing = 0

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
Safe(b) ==
  LET m == Cardinality(bank[b] \cap Missionaries)
      c == Cardinality(bank[b] \cap Cannibals)
  IN m = 0 \/ c <= m

\* The boat carries at least one person and at most two; it never travels empty.
Move ==
  /\ crossing' = 0
  /\ \E g \in SUBSET bank[boatAt] :
       /\ Cardinality(g) \in 1..2
       /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east" IN
            /\ bank' = [bank EXCEPT ![boatAt] = @ \ g, ![dest] = @ \cup g]
            /\ boatAt' = dest
  /\ \A b \in Banks : Safe(b)

Next == Move

\* The puzzle is solved when the east bank is empty (everyone reached the west).
Solution == \A b \in Banks : Safe(b)

Spec == Init /\ [][Next]_vars

====