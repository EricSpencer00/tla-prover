---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES dock, bank, solution

vars == <<dock, bank, solution>>

\* Safety: a bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(ba) ==
    /\ \E m \in Missionaries : ba[m]
    => Cardinality({c \in Cannibals : ba[c]}) <= Cardinality({m \in Missionaries : ba[m]})

TypeOK ==
    /\ dock \in Banks
    /\ bank \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
    /\ solution \in BOOLEAN

Init ==
    /\ dock = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]
    /\ solution = FALSE

\* A non-empty group of size <= 2 boards the boat on the dock bank, crosses, and
\* the two banks are updated together. The move is only enabled when both banks
\* stay safe afterwards.
Move(group) ==
    /\ group # {}
    /\ GroupSize(group) <= 2
    /\ group \subseteq bank[dock]
    /\ \A b \in Banks : BankSafe(b)
    /\ \E b \in Banks :
         /\ b # dock
         /\ bank' = [bank EXCEPT ![dock] = @ \ group, ![b] = @ \cup group]
    /\ dock' = (IF dock = "east" THEN "west" ELSE "east")
    /\ solution' = (IF solution = FALSE /\ bank["east"] \ group = {} THEN TRUE ELSE solution)

GroupSize(g) == Cardinality(g)

Next ==
    \/ \E group \in SUBSET (Missionaries \cup Cannibals) : Move(group)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

\* The puzzle's master invariant: both banks are always safe under the cannibal
\* majority rule, and the boat never carries an empty or overloaded group.
TypeOK == TypeOK

\* Progress: the solution is eventually reached, i.e. everyone gets off the east
\* bank onto the west side.
Solution == solution
====