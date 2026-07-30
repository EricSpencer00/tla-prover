---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boat, bankPeople
vars == <<boat, bankPeople>>

RECURSIVE Count(_, _)
Count(S, f) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Count(S \ {x}, f)

BankPeopleToSet(B) == bankPeople[B]

RECURSIVE BankSet(_, _)
BankSet(S, f) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] \cup BankSet(S \ {x}, f)

People == Missionaries \cup Cannibals

TypeOK ==
  /\ boat \in Banks
  /\ bankPeople \in [Banks -> SUBSET People]

Init ==
  /\ boat = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

MissionaryOnBank(b) == {p \in bankPeople[b] : p \in Missionaries}
CannibalOnBank(b) == {p \in bankPeople[b] : p \in Cannibals}

CannotOutnumberMissionaries ==
  /\ \A b \in Banks :
       ~(MissionaryOnBank(b) # {} /\ Cardinality(CannibalOnBank(b)) > Cardinality(MissionaryOnBank(b)))
  /\ \A b \in Banks : Cardinality(bankPeople[b]) <= 4

\* Boarding and crossing is a single atomic action here, which is what lets the
\* safety check on the resulting distribution be applied before the move happens.
Move(S) ==
  /\ S \subseteq bankPeople[boat]
  /\ Cardinality(S) \in {1, 2}
  /\ boat' = IF boat = "east" THEN "west" ELSE "east"
  /\ bankPeople' = [bankPeople EXCEPT ![boat] = @ \ S, ![IF boat = "east" THEN "west" ELSE "east"] = @ \cup S]
  /\ CannotOutnumberMissionaries

Next ==
  \/ \E S \in SUBSET People : Move(S)

Spec == Init /\ [][Next]_vars

\* The east bank must eventually empty; a model checker finding this invariant
\* violated elsewhere will emit a trace where the east bank never empties,
\* which is exactly the solution to the puzzle.
Solution ==
  /\ CannotOutnumberMissionaries
  /\ bankPeople["east"] # {}

====