---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boat, bank
vars == <<boat, bank>>

\* A bank is safe if it either has no missionaries or the cannibals there
\* are not outnumbering them: with no missionaries, any cannibal count is fine.
TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ \A s \in Banks:
       \/ bank[s] \cap Missionaries = {}
       \/ Cardinality(bank[s] \cap Cannibals) <= Cardinality(bank[s] \cap Missionaries)

Init ==
  /\ boat = "east"
  /\ bank = [s \in Banks |-> IF s = "east" THEN People ELSE {}]

Move(group) ==
  /\ group \subseteq bank[boat]
  /\ Cardinality(group) \in 1..2
  /\ LET opposite == CHOOSE t \in Banks : t # boat IN
       /\ bank' = [bank EXCEPT ![boat] = bank[boat] \ group, ![opposite] = bank[opposite] \cup group]
       /\ boat' = opposite
  /\ \A s \in Banks:
       \/ bank[s] \cap Missionaries = {}
       \/ Cardinality(bank[s] \cap Cannibals) <= Cardinality(bank[s] \cap Missionaries)

Next == \E g \in SUBSET People : Move(g)

Solution ==
  /\ \A s \in Banks:
       \/ bank[s] \cap Missionaries = {}
       \/ Cardinality(bank[s] \cap Cannibals) <= Cardinality(bank[s] \cap Missionaries)
  /\ Cardinality(bank["west"] \cap People) >= 1

Spec == Init /\ [][Next]_vars

====