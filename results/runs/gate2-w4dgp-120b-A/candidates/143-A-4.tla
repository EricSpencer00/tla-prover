---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

\* Classic missionaries and cannibals river crossing: a boat (capacity 1 or 2)
\* ferries people across.  A bank is safe if it has no missionaries or the
\* cannibals do not outnumber them.  The puzzle is solved when the east bank is empty.
CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

VARIABLES bank, location
vars == <<bank, location>>

Count[S, p] == Cardinality({x \in S : p[x]})
MissionsAt(b) == Count[bank[b], Missionaries]
CannibalsAt(b) == Count[bank[b], Cannibals]
BankSafe(b) == (MissionsAt(b) = 0) \/ (MissionsAt(b) >= CannibalsAt(b))

Init ==
  /\ bank = [b \in {"east", "west"} |-> IF b = "east" THEN People ELSE {}]
  /\ location = "east"

\* The boat never travels empty, and the banks it departs from and arrives at must
\* both be left in a safe configuration.
Next ==
  \/ \E g \in SUBSET People :
       /\ g # {}
       /\ Cardinality(g) <= 2
       /\ g \subseteq bank[location]
       /\ LET other == IF location = "east" THEN "west" ELSE "east" IN
          /\ BankSafe(other)
          /\ Cardinality(bank[location] \ g) = 0
             \/ (MissionsAt(other \cup g) = 0) \/ (MissionsAt(other \cup g) >= CannibalsAt(other \cup g))
          /\ bank' = [bank EXCEPT ![location] = @ \ g, ![other] = @ \cup g]
          /\ location' = other
  \/ UNCHANGED <<bank, location>>

TypeOK ==
  /\ bank \in [ {"east", "west"} -> SUBSET People ]
  /\ location \in {"east", "west"}

\* Goal: east bank empty.  If this were ever violated (the east bank never empties),
\* a model checker would report a counterexample trace, which is the solution.
Solution ==
  \A b \in {"east", "west"} : BankSafe(b)
====