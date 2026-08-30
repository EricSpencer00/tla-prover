---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boat, population

vars == <<boat, population>>

PopCount(b, g) == Cardinality({p \in g : population[b][p]})

TypeOK ==
    /\ boat \in Banks
    /\ population \in [Banks -> [Missionaries \cup Cannibals -> BOOLEAN]]

Init ==
    /\ boat = "east"
    /\ population = [b \in Banks |-> [p \in Missionaries \cup Cannibals |-> b = "east"]]

\* A bank with no missionaries is safe by default; otherwise cannibals must not
\* outnumber missionaries.
BankSafe(b) ==
    IF PopCount(b, Missionaries) = 0 THEN TRUE
    ELSE PopCount(b, Cannibals) <= PopCount(b, Missionaries)

\* The boat carries exactly one or two people across the river; it can never
\* travel empty or overloaded, and the move is only allowed if both banks stay safe.
Move ==
    \E S \in SUBSET Missionaries \cup Cannibals :
        /\ Cardinality(S) \in 1..2
        /\ \A p \in S : population[boat][p]
        /\ LET dest == IF boat = "east" THEN "west" ELSE "east" IN
            /\ \A p \in S : population' = [population EXCEPT ![boat][p] = FALSE, ![dest][p] = TRUE]
            /\ boat' = dest
        /\ BankSafe("east") /\ BankSafe("west")

Next == Move

\* Safety: missionaries are never outnumbered on a bank, and the boat is never
\* sent across empty or with too many people.
TypeOK == TypeOK
Solution == BankSafe("east") /\ BankSafe("west")

====