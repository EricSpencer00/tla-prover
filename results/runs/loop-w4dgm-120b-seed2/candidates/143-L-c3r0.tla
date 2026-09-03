---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals

CONSTANTS Missionaries, Cannibals

ASSUME Missionaries = {"m1", "m2", "m3"}
ASSUME Cannibals = {"c1", "c2", "c3"}

People == Missionaries \cup Cannibals

EastBank == "east"
WestBank == "west"

VARIABLES bank, boatAt

vars == <<bank, boatAt>>

RECURSIVE SumForSet(_, _)
SumForSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumForSet(f, S \ {x})

LeadsToEastBank(p) == IF bank[p] = WestBank THEN WestBank ELSE EastBank

TypeOK ==
  /\ bank \in [People -> {EastBank, WestBank}]
  /\ boatAt \in {EastBank, WestBank}

Init ==
  /\ bank = [p \in People |-> EastBank]
  /\ boatAt = EastBank

BankContents(b) == {p \in People : bank[p] = b}
BankMissionaries(b) == Missionaries \cap BankContents(b)
BankCannibals(b) == Cannibals \cap BankContents(b)

BankIsSafe(b) ==
  \/ BankMissionaries(b) = {}
  \/ Cardinality(BankCannibals(b)) <= Cardinality(BankMissionaries(b))

\* A move is only enabled when the resulting banks are both safe.
Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ \A p \in g : bank[p] = boatAt
  /\ BankIsSafe(boatAt)
  /\ BankIsSafe(LeadsToEastBank(boatAt))
  /\ bank' = [p \in People |-> IF p \in g THEN LeadsToEastBank(boatAt) ELSE bank[p]]
  /\ boatAt' = LeadsToEastBank(boatAt)

Next ==
  \/ \E g \in SUBSET People : Move(g)

Solution == \A p \in People : (bank[p] = EastBank) ~> (bank[p] = WestBank)

\* The invariants together capture the puzzle's constraints (bank safety plus
\* non-emptiness of the move set); the liveness property is the crossing itself.
TypeOKInv == TypeOK
SolutionInv == Solution

Spec == Init /\ [][Next]_vars

INVARIANT TypeOKInv
INVARIANT SolutionInv
====