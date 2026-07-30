---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Cardinality(Missionaries) = 3 /\ Cardinality(Cannibals) = 3

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
NoBank == "none"
MaxWin == 3

VARIABLES boatAt, bank, traveled

vars == <<boatAt, bank, traveled>>

\* The count of missionaries on a bank, derived from the set of people there.
MissionariesOn(b) == Cardinality(bank[b] \cap Missionaries)

CannibalsOn(b) == Cardinality(bank[b] \cap Cannibals)

\* Both banks safe: missionaries never outnumbered by cannibals wherever they are present.
BankSafe(b) == ~ (MissionariesOn(b) > 0 /\ CannibalsOn(b) > MissionariesOn(b))

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ traveled \in 0..MaxWin

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ traveled = 0

Move(group) ==
  /\ group \subseteq bank[boatAt]
  /\ Cardinality(group) \in {1, 2}
  /\ \A b \in Banks : BankSafe(b) /\ BankSafe(b) /\ Cardinality((bank[b] \ group) \cup (bank[IF b = boatAt THEN "west" ELSE "east"] \cup group) \cap Missionaries) <= 3

  /\ bank' = [b \in Banks |-> IF b = boatAt
                 THEN bank[b] \ group
                 ELSE IF b = (IF boatAt = "east" THEN "west" ELSE "east")
                      THEN bank[b] \cup group
                      ELSE bank[b]]
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
  /\ traveled' = (traveled + 1) % (MaxWin + 1)

Next ==
  \/ \E group \in SUBSET People : Move(group)

Spec == Init /\ [][Next]_vars

\* No missionaries are eaten anywhere on either bank.
Solution == \A b \in Banks : BankSafe(b)

====