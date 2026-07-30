---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES boat, bank
vars == <<boat, bank>>

TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET People]

\* The puzzle is solved when the departure bank (east) is empty, so
\* the invariant reads "non-empty" and a violation is the solution.
BankSafe(b) ==
  \/ Missionaries \cap bank[b] = {}
  \/ Cardinality(Cannibals \cap bank[b]) <= Cardinality(Missionaries \cap bank[b])

\* A crossing always moves someone.
Move ==
  /\ \E src \in Banks, dst \in Banks :
       /\ src # dst
       /\ \E s \in SUBSET bank[src] :
            /\ s # {}
            /\ Cardinality(s) <= 2
            /\ bank' = [bank EXCEPT ![src] = @ \ s, ![dst] = @ \cup s]
       /\ boat' = dst
  /\ BankSafe("east")
  /\ BankSafe("west")

Next == Move

Init ==
  /\ boat = "east"
  /\ bank = [b \in Banks |->
               IF b = "east" THEN People ELSE {}]

Solution == BankSafe("east")

====