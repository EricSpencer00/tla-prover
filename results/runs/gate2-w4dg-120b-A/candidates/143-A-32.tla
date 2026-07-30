---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
BoatCap == 2

VARIABLES boatAt, peopleAt
vars == <<boatAt, peopleAt>>

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumSet(f, S \ {x})

TypeOK ==
  /\ boatAt \in Banks
  /\ peopleAt \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ peopleAt = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* Safety on a bank: no missionaries or cannibals do not outnumber them.
BankSafe(b) ==
  LET ms == Missionaries \cap peopleAt[b] IN
  LET cs == Cannibals \cap peopleAt[b] IN
    \/ ms = {}
    \/ Cardinality(cs) <= Cardinality(ms)

Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= BoatCap
  /\ g \subseteq peopleAt[boatAt]
  /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east" IN
       /\ peopleAt' = [peopleAt EXCEPT ![boatAt] = @ \ g, ![dest] = @ \cup g]
       /\ boatAt' = dest
  /\ BankSafe("east") /\ BankSafe("west")

Next ==
  \/ \E g \in (SUBSET People) : Move(g)

Spec == Init /\ [][Next]_vars

\* A solution is reached when the east bank is empty; the spec is designed so
\* that a model checker violating this invariant actually exhibits the trace.
Solution == peopleAt["east"] = {}

====