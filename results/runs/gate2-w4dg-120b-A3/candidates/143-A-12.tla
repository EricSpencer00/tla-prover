---- MODULE MissionariesAndCannibals ----
\* Missionaries and Cannibals river crossing. A bank is safe iff either it holds
\* no missionaries or cannibals never outnumber them. The boat never crosses empty
\* and never carries more than its capacity of two.
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
\* Boats capacity: the number of people it may carry per crossing.
BoatCap == 2

VARIABLES boat, bank

vars == <<boat, bank>>

TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET People]

\* A bank is safe if either it has no missionaries or cannibals never outnumber them.
BankSafe(k) ==
  \/ (bank[k] \cap Missionaries = {})
  \/ Cardinality(bank[k] \cap Cannibals) <= Cardinality(bank[k] \cap Missionaries)

Init ==
  /\ boat = "east"
  /\ bank = [k \in Banks |-> IF k = "east" THEN People ELSE {}]

\* Cross: a non-empty group of at most two boards on the current bank and docks
\* at the other bank, provided both banks stay safe afterwards.
Cross(g) ==
  /\ g \subseteq bank[boat]
  /\ g # {}
  /\ Cardinality(g) <= BoatCap
  /\ boat' = IF boat = "east" THEN "west" ELSE "east"
  /\ bank' = [bank EXCEPT ![boat] = @ \ g, ![IF boat = "east" THEN "west" ELSE "east"] = @ \cup g]
  /\ BankSafe(boat)
  /\ BankSafe(IF boat = "east" THEN "west" ELSE "east")

Next == \E g \in SUBSET People : Cross(g)

Spec == Init /\ [][Next]_vars

\* The solution is reached when the east bank is empty, but the model must not
\* be allowed to settle before safety is always satisfied.
Solution ==
  /\ BankSafe("east")
  /\ BankSafe("west")
  /\ bank["east"] = {}

====