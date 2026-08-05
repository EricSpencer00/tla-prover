---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

NoOne == "none"
Banks == {"east", "west"}

VARIABLES boat, bank

vars == <<boat, bank>>

TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
  /\ boat = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

Move(S) ==
  /\ S # {}
  /\ S \subseteq bank[boat]
  /\ Cardinality(S) <= 2
  /\ bank' = [bank EXCEPT ![boat] = @ \ S, ![IF boat = "east" THEN "west" ELSE "east"] = @ \cup S]
  /\ boat' = IF boat = "east" THEN "west" ELSE "east"

Next ==
  \E S \in (SUBSET (Missionaries \cup Cannibals)):
    Move(S)

Solution ==
  /\ bank["west"] = Missionaries \cup Cannibals

Spec == Init /\ [][Next]_vars

====