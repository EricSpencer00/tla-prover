---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
BoatCap == 2

VARIABLES boatAt, bankPeople

vars == <<boatAt, bankPeople>>

RECURSIVE Count(_, _)
Count(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Count(f, S \ {x})

MissionariesOn(b) == Count([p \in People |-> IF p \in Missionaries THEN 1 ELSE 0], bankPeople[b])
CannibalsOn(b) == Count([p \in People |-> IF p \in Cannibals THEN 1 ELSE 0], bankPeople[b])

TypeOK ==
  /\ boatAt \in Banks
  /\ bankPeople \in [Banks -> SUBSET People]

Init ==
  /\ boatAt = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(b) ==
  \/ MissionariesOn(b) = 0
  \/ CannibalsOn(b) <= MissionariesOn(b)

\* The boat must always carry at least one person and never more than its cap.
BoatLoadValid(g) == g # {} /\ Cardinality(g) <= BoatCap

Move(g) ==
  /\ BoatLoadValid(g)
  /\ g \subseteq bankPeople[boatAt]
  /\ LET other == IF boatAt = "east" THEN "west" ELSE "east" IN
       /\ bankPeople' = [bankPeople EXCEPT ![boatAt] = @ \ g, ![other] = @ \cup g]
       /\ boatAt' = other
  /\ BankSafe("east")
  /\ BankSafe("west")

Next == \E g \in SUBSET People : Move(g)

Spec == Init /\ [][Next]_vars

\* The puzzle is solved when the east bank is empty; a model checker that
\* flags a violation of this invariant has found a solution trace.
Solution == bankPeople["east"] = {}

====