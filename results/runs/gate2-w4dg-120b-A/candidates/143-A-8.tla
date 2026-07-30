---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Missionaries,
  Cannibals

People == Missionaries \cup Cannibals
Banks == {"west", "east"}
BoatCapacity == 2

VARIABLES
  boatAt,
  onBank

vars == <<boatAt, onBank>>

TypeOK ==
  /\ boatAt \in Banks
  /\ onBank \in [Banks -> SUBSET People]

\* The bank a person is on is exactly determined by the onBank mapping.
BankOf(p) == CHOOSE b \in Banks : p \in onBank[b]

BankCounts(b) ==
  [ms |-> Cardinality({p \in onBank[b] : p \in Missionaries}),
   cs |-> Cardinality({p \in onBank[b] : p \in Cannibals})]

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(b) == (BankCounts(b).ms = 0) \/ (BankCounts(b).cs <= BankCounts(b).ms)

\* The whole system is safe iff every bank is safe.
Solution == \A b \in Banks : BankSafe(b)

Init ==
  /\ boatAt = "east"
  /\ onBank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* One or two people board the boat on the current bank and go to the other one.
Move ==
  /\ \E group \in SUBSET Missionaries \cup Cannibals :
       /\ Cardinality(group) \in {1, 2}
       /\ group \subseteq onBank[boatAt]
       /\ onBank' = [b \in Banks |->
                        IF b = boatAt
                          THEN onBank[b] \ group
                          ELSE onBank[b] \cup group]
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next == Move

Spec == Init /\ [][Next]_vars

\* Every bank is safe and the boat never sits empty or overloaded.
TypeOK == TypeOK /\ Solution

====