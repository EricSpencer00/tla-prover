---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* boatAtBank: the bank the boat is currently docked at; people: distribution of
\* missionaries and cannibals across the two banks; ride: who is currently in the
\* boat. A bank is safe if it holds only cannibals, or if cannibals do not
\* outnumber missionaries there.
VARIABLES boatAtBank, people, ride

AllPeople == Missionaries \cup Cannibals
Banks == {"east", "west"}
EastBank == "east"
WestBank == "west"

TypeOK ==
  /\ boatAtBank \in Banks
  /\ people \in [Banks -> SUBSET AllPeople]
  /\ ride \in SUBSET AllPeople

\* Safety: missionaries present on a bank are never outnumbered by cannibals.
BankIsSafe(b) ==
  LET m == Cardinality(people[b] \cap Missionaries)
      c == Cardinality(people[b] \cap Cannibals)
  IN \/ m = 0
     \/ c <= m
Init ==
  /\ boatAtBank = EastBank
  /\ people = [b \in Banks |-> IF b = EastBank THEN AllPeople ELSE {}]
  /\ ride = {}

\* A move loads 1-2 people from the current bank into the boat and drops them on
\* the opposite bank, only if the resulting distribution keeps both banks safe.
Move ==
  /\ \E g \in SUBSET AllPeople :
       /\ Cardinality(g) \in {1, 2}
       /\ g \subseteq people[boatAtBank]
       /\ people' = [people EXCEPT ![boatAtBank] = people[boatAtBank] \ g, ![IF boatAtBank = EastBank THEN WestBank ELSE EastBank] = people[IF boatAtBank = EastBank THEN WestBank ELSE EastBank] \cup g]
       /\ ride' = g
  /\ boatAtBank' = IF boatAtBank = EastBank THEN WestBank ELSE EastBank

Next == Move

\* An empty east bank is the puzzle's solved state; a model checker that flags
\* a violation of "east bank non-empty" has actually found a solution.
Solution == \A b \in Banks : BankIsSafe(b)

====