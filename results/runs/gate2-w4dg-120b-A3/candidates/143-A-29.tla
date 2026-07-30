---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Missionaries,
  Cannibals

VARIABLES
  boatBank,
  bankPeople

vars == <<boatBank, bankPeople>>

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
BoatSizes == {1, 2}

RECURSIVE Count(_, _)
Count(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + Count(f, S \ {x})

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(bk) ==
  \/ (\A p \in bankPeople[bk] : p \notin Missionaries)
  \/ Count([p \in People |-> IF p \in Missionaries THEN 1 ELSE 0], bankPeople[bk]) >=
     Count([p \in People |-> IF p \in Cannibals THEN 1 ELSE 0], bankPeople[bk])

TypeOK ==
  /\ boatBank \in Banks
  /\ bankPeople \in [Banks -> SUBSET People]

Init ==
  /\ boatBank = "east"
  /\ bankPeople = [bk \in Banks |-> IF bk = "east" THEN People ELSE {}]

\* Exactly the people in grp leave the source bank; everyone in grp arrives at the other bank.
Move(grp) ==
  /\ grp \subseteq People
  /\ grp # {}
  /\ Cardinality(grp) \in BoatSizes
  /\ grp \subseteq bankPeople[boatBank]
  /\ bankPeople' = [bankPeople EXCEPT ![boatBank] = @ \ grp, ![IF boatBank = "east" THEN "west" ELSE "east"] = @ \cup grp]
  /\ boatBank' = IF boatBank = "east" THEN "west" ELSE "east"
  /\ /\ BankSafe("east")
     /\ BankSafe("west")

Next == \E grp \in SUBSET People : Move(grp)

Spec == Init /\ [][Next]_vars

Solution == \A bk \in Banks : BankSafe(bk)

====