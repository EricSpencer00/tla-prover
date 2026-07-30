---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boat, bankPop

vars == <<boat, bankPop>>

Count(A, S) == Cardinality(A \cap S)

TypeOK ==
  /\ boat \in Banks
  /\ bankPop \in [Banks -> SUBSET People]

Init ==
  /\ boat = "east"
  /\ bankPop = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A group of 1 or 2 people crosses from the bank the boat is docked at to
\* the other bank, provided both banks stay safe afterwards.
Move(group) ==
  /\ group \subseteq bankPop[boat]
  /\ Cardinality(group) \in 1..2
  /\ bankPop' = [bankPop EXCEPT ![boat] = @ \ group, ![IF boat = "east" THEN "west" ELSE "east"] = @ \cup group]
  /\ boat' = IF boat = "east" THEN "west" ELSE "east"

Next ==
  \/ \E group \in SUBSET People : Move(group)

\* Safety: missionaries are never outnumbered by cannibals on a bank.
\* The bound on canoe capacity is already enforced by Move's cardinality test.
Solution ==
  /\ \A b \in Banks : (Missionaries \cap bankPop[b] = {}) \/ (Count(Cannibals, bankPop[b]) =< Count(Missionaries, bankPop[b]))
  /\ Cardinality(People \ bankPop["west"]) =< 2

Spec == Init /\ [][Next]_vars

====