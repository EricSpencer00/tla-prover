---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS
  Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES
  boat, bankDist

TypeOK ==
  /\ boat \in Banks
  /\ bankDist \in [Banks -> SUBSET People]

\* A bank is safe if it contains only cannibals (no missionaries to endanger)
\* or if cannibals do not outnumber missionaries there.
BankSafe(b) ==
  LET m == Cardinality(Missionaries \cap bankDist[b]) IN
  LET c == Cardinality(Cannibals \cap bankDist[b]) IN
  \/ m = 0
  \/ c <= m

Init ==
  /\ boat = "east"
  /\ bankDist = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A group of one or two people boards the boat at the current bank and
\* crosses, but only if the resulting banks are both safe.
Move(g) ==
  /\ g \subseteq bankDist[boat]
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ LET dest == IF boat = "east" THEN "west" ELSE "east" IN
       /\ Cardinality(bankDist[dest] \cup g) <= Cardinality(bankDist[dest]) + 2
       /\ bankDist' = [bankDist EXCEPT ![boat] = bankDist[boat] \ g, ![dest] = @ \cup g]
       /\ boat' = dest

Next ==
  \/ \E g \in SUBSET People : Move(g)

\* The solution is reached once the east bank is empty.
Solution == \A b \in Banks : BankSafe(b) /\ bankDist["east"] = {}

====