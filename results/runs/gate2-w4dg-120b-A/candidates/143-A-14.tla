---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

Banks == {"east", "west"}
TransferSizes == 1..2
Pool == Missionaries \cup Cannibals

VARIABLES boat, bankOf

TypeOK ==
  /\ boat \in Banks
  /\ bankOf \in [Banks -> SUBSET People]

Init ==
  /\ boat = "east"
  /\ bankOf = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank may host only cannibals safely; otherwise cannibals must not outnumber missionaries.
BankIsSafe(b) ==
  LET people == bankOf[b] IN
  LET mc == Cardinality(people \cap Missionaries) IN
  LET cc == Cardinality(people \cap Cannibals) IN
    \/ mc = 0
    \/ cc <= mc

\* The move lifts a nonempty group from the current bank, lands it on the other side, and
\* leaves the boat docked at the destination bank.
Move ==
  \E g \in SUBSET People :
    /\ g # {}
    /\ Cardinality(g) \in TransferSizes
    /\ g \subseteq bankOf[boat]
    /\ LET dest == IF boat = "east" THEN "west" ELSE "east" IN
         /\ bankOf' = [bankOf EXCEPT ![boat] = @ \ g, ![dest] = @ \cup g]
         /\ boat' = dest
    /\ BankIsSafe("east")
    /\ BankIsSafe("west")

Next == Move

Spec == Init /\ [][Next]_<<boat, bankOf>>

\* The east bank must not become permanently empty: a deadlock with everyone across
\* would leave no further moves, and TLC would report the invariant violation.
Solution == \A b \in Banks : BankIsSafe(b)

====