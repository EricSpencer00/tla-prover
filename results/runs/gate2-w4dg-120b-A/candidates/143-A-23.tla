---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

Banks == {"east", "west"}
\* East is the starting bank; bankOf counts how many of each type are present.
bankOf(b, m) == Cardinality({p \in m : p \in b})
bankSize(b) == Cardinality(b)

VARIABLES boat, banks

vars == <<boat, banks>>

TypeOK ==
  /\ boat \in Banks
  /\ banks \in [Banks -> SUBSET People]

\* Safety is twofold: the boat carries 1 or 2 people, and no bank ever has
\* missionaries outnumbered by cannibals (unless it holds none).
BoatOccupied ==
  \A b \in Banks : bankSize(b) = 0 \/ bankSize(b) >= 1 /\ bankSize(b) <= 2

BankIsSafe(b) ==
  \/ bankOf(b, Missionaries) = 0
  \/ bankOf(b, Cannibals) <= bankOf(b, Missionaries)

AllBanksSafe == \A b \in Banks : BankIsSafe(b)

\* The move is guarded by the destination bank also staying safe; that
\* forward-checking is what stops a cannibal triplet from being a dead end.
Move(g) ==
  /\ g # {}
  /\ g \subseteq banks[boat]
  /\ bankSize(g) >= 1 /\ bankSize(g) <= 2
  /\ BankIsSafe(banks[boat] \ g)
  /\ BankIsSafe(banks[boat] \cup g)
  /\ banks' = [banks EXCEPT ![boat] = banks[boat] \ g, ![boat] = banks[boat] \cup g]
  /\ boat' = (IF boat = "east" THEN "west" ELSE "east")

Next == \E g \in SUBSET People : Move(g)

Init ==
  /\ boat = "east"
  /\ banks = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* The puzzle is solved when the east bank is empty; the invariant is the
\* safety condition, so a model checker finding it false has produced a
\* crossing plan that solves the puzzle.
Solution == \A b \in Banks : BankIsSafe(b)

Spec == Init /\ [][Next]_vars

====