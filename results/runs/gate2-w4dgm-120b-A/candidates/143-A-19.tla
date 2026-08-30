---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \union Cannibals
MoveSizes == {1, 2}

VARIABLES boatAt, bank

vars == <<boatAt, bank>>

RECURSIVE SumOnBank(_)
SumOnBank(g) ==
  IF g = {} THEN 0
  ELSE LET x == CHOOSE y \in g : TRUE
       IN 1 + SumOnBank(g \ {x})

BankIsSafe(b) ==
  \/ bank[b] \cap Missionaries = {}
  \/ Cardinality(bank[b] \cap Cannibals) <= Cardinality(bank[b] \cap Missionaries)

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move(S) ==
  /\ S \subseteq bank[boatAt]
  /\ S # {}
  /\ Cardinality(S) \in MoveSizes
  /\ LET newBank == [bank EXCEPT ![boatAt] = bank[boatAt] \ S,
                                   ![IF boatAt = "east" THEN "west" ELSE "east"] = bank[IF boatAt = "east" THEN "west" ELSE "east"] \union S]
     IN /\ BankIsSafe("east")
        /\ BankIsSafe("west")
        /\ bank' = newBank
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"

Next ==
  \/ \E S \in SUBSET People : Move(S)

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET People]

Solution ==
  /\ bank["west"] = People
  /\ Cardinality(bank["east"]) = 0
  /\ boatAt = "west"

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

====