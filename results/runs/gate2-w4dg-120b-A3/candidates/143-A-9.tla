---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boatAt, bank

vars == <<boatAt, bank>>

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank is safe if it holds only cannibals, or cannibals do not outnumber
\* missionaries (count on the safe side: <= instead of <).
BankSafe(b) ==
  LET ms == {p \in bank[b] : p \in Missionaries}
      cs == {p \in bank[b] : p \in Cannibals}
  IN Cardinality(ms) = 0 \/ Cardinality(cs) <= Cardinality(ms)

Move(p) ==
  /\ p \subseteq bank[boatAt]
  /\ Cardinality(p) \in {1, 2}
  /\ Cardinality(p) >= 1 /\ Cardinality(p) <= 2
  /\ LET dest == IF boatAt = "east" THEN "west" ELSE "east"
         newBank == [bank EXCEPT ![boatAt] = bank[boatAt] \ p, ![dest] = @ \cup p]
     IN /\ newBank["east"] \subseteq People
        /\ newBank["west"] \subseteq People
        /\ BankSafe("east")
        /\ BankSafe("west")
        /\ bank' = newBank
        /\ boatAt' = dest
  /\ UNCHANGED <<>>

Next == \E p \in SUBSET People : Move(p)

Spec == Init /\ [][Next]_vars

Solution == bank["east"] # {}

====