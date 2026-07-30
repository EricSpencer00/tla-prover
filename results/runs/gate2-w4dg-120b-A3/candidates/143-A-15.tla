---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boat, people

vars == <<boat, people>>

TypeOK ==
  /\ boat \in Banks
  /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
  /\ boat = "east"
  /\ people = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* Missionaries are only ever endangered on a bank that already has some; a
\* bank of pure cannibals or of pure missionaries is safe by definition.
BankSafe(b) ==
  /\ (people[b] \cap Missionaries = {}) \/ Cardinality(people[b] \cap Cannibals) <= Cardinality(people[b] \cap Missionaries)

\* A move crosses a non-empty group of size one or two and demands both banks
\* to stay safe afterwards, so the capacity rule and the safety rule are carried
\* together and can never pull apart.
Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ g \subseteq people[boat]
  /\ \E dest \in Banks \ {boat} :
       /\ people' = [people EXCEPT ![boat] = @ \ g, ![dest] = @ \cup g]
       /\ boat' = dest
  /\ UNCHANGED <<>>

Next ==
  \/ \E g \in SUBSET (Missionaries \cup Cannibals) : Move(g)
  \/ \E b \in Banks : /\ b # boat
                       /\ people' = [people EXCEPT ![boat] = {}, ![b] = people[b] \cup people[boat]]
                       /\ boat' = b

Solution == \A b \in Banks : BankSafe(b)

Spec == Init /\ [][Next]_vars

====