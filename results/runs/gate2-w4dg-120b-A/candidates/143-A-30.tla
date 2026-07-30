---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Missionaries,
    Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
PeopleAt(b) == Cardinality({p \in People : b[p]})

VARIABLES dock, b

vars == <<dock, b>>

TypeOK ==
    /\ dock \in Banks
    /\ b \in [Banks -> SUBSET People]

Init ==
    /\ dock = "east"
    /\ b = [k \in Banks |-> IF k = "east" THEN People ELSE {}]

\* A bank is safe if it has no missionaries, or its cannibals do not outnumber
\* its missionaries -- that phrasing is exactly what the additional_assumptions
\* item calls out as the intended meaning.
BankSafe(k) ==
    LET m == Cardinality({p \in b[k] : p \in Missionaries})
        c == Cardinality({p \in b[k] : p \in Cannibals})
    IN \/ m = 0
       \/ c <= m

\* The crossing must also respect the boat capacity: it carries one or two
\* people, never zero and never more than the boat can hold.
Move ==
    /\ \E g \in SUBSET b[dock] :
         /\ g # {}
         /\ Cardinality(g) <= 2
         /\ BankSafe("east") /\ BankSafe("west")
         /\ LET other == IF dock = "east" THEN "west" ELSE "east" IN
              /\ b' = [b EXCEPT ![dock] = @ \ g, ![other] = @ \cup g]
              /\ dock' = other

Next ==
    \/ Move

Spec == Init /\ [][Next]_vars

\* The east bank non-empty invariant is the puzzle's "solution": a violation
\* means the east bank was emptied, which is what the model checker will
\* report as a counterexample and which is the solution trace.
Solution ==
    /\ \A k \in Banks : BankSafe(k)
    /\ b["east"] # {}

====