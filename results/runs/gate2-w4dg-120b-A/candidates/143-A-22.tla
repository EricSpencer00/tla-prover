---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

AllPeople == Missionaries \cup Cannibals

VARIABLES boatAt, bankPeople
vars == <<boatAt, bankPeople>>

Banks == {"east", "west"}

\* The set of people riding in the boat right now. It is a derived value, not a
\* separate variable: whatever is currently being carried is simply missing from
\* the bank it left (and will be missing from the opposite bank until it lands).
Riding == { p \in AllPeople : p \notin bankPeople[boatAt] }

TypeOK ==
  /\ boatAt \in Banks
  /\ bankPeople \in [Banks -> SUBSET AllPeople]

BankOK(b) == Cardinality(bankPeople[b] \cap Missionaries) > 0 =>
              Cardinality(bankPeople[b] \cap Cannibals) <= Cardinality(bankPeople[b] \cap Missionaries)

\* A bank with only cannibals is safe (nothing to eat), as is a bank with no people.
Init ==
  /\ boatAt = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]

\* People move in groups of size 1 or 2; the boat never travels empty.
Move ==
  /\ \E g \in SUBSET AllPeople :
       /\ Cardinality(g) \in 1..2
       /\ g \subseteq bankPeople[boatAt]
       /\ \E nb \in Banks \ {boatAt} :
            /\ \A b \in Banks : Cardinality(bankPeople[b] \cup g) <= Cardinality(bankPeople[b])
            /\ \A b \in Banks : Cardinality(bankPeople[b] \cup g) >= Cardinality(bankPeople[b])
            /\ bankPeople' = [bankPeople EXCEPT ![boatAt] = @ \ g, ![nb] = @ \cup g]
            /\ boatAt' = nb
  /\ UNCHANGED <<>>

Next == Move

Spec == Init /\ [][Next]_vars

Solution == bankPeople["east"] # {}

====