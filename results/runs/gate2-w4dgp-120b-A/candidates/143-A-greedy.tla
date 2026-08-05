---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boat, bank

vars == <<boat, bank>>

\* A bank is safe if it has no missionaries, or the cannibals there do not
\* outnumber the missionaries (the puzzle's safety condition).
Safe(b) == (bank[b] \cap Missionaries = {}) \/ (Cardinality(bank[b] \cap Cannibals) <= Cardinality(bank[b] \cap Missionaries))

TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET People]

Init ==
  /\ boat = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A crossing carries one or two people; the boat never travels empty.
Move(S) ==
  /\ S # {}
  /\ Cardinality(S) <= 2
  /\ S \subseteq bank[boat]
  /\ LET other == IF boat = "east" THEN "west" ELSE "east" IN
       /\ bank' = [bank EXCEPT ![boat] = @ \ S, ![other] = @ \cup S]
       /\ boat' = other

Next == \E S \in SUBSET People : Move(S)

\* The puzzle is solved when the east bank is empty (everyone reached the west).
Solution == bank["east"] = {}

Spec == Init /\ [][Next]_vars

====