---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals
AllPeople == Missionaries \cup Cannibals
Banks == {"east", "west"}
BoatCap == 2

VARIABLES boat, bank
vars == <<boat, bank>>

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumSet(f, S \ {x})

BoatLoad(S) == SumSet([x \in S |-> 1], S)

TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET AllPeople]

\* A bank is safe if it has no missionaries to endanger, or if cannibals
\* do not outnumber missionaries there.
BankSafe(b) ==
  LET cr == Cardinality(bank[b] \cap Cannibals)
      mr == Cardinality(bank[b] \cap Missionaries)
  IN (mr = 0) \/ (cr <= mr)

\* Every crossing must leave both banks safe.
MoveLegal(S) ==
  /\ BoatLoad(S) >= 1
  /\ BoatLoad(S) <= BoatCap
  /\ S \subseteq bank[boat]
  /\ LET newBank == [bank EXCEPT ![boat] = bank[boat] \ S, ![IF boat = "east" THEN "west" ELSE "east"] = bank[IF boat = "east" THEN "west" ELSE "east"] \cup S]
     IN /\ BankSafe(boat)
        /\ BankSafe(IF boat = "east" THEN "west" ELSE "east")

Init ==
  /\ boat = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]

Next ==
  /\ \E S \in SUBSET AllPeople : MoveLegal(S)
  /\ boat' = IF boat = "east" THEN "west" ELSE "east"
  /\ UNCHANGED bank

Spec == Init /\ [][Next]_vars

\* The puzzle is solved once the start bank is empty.
Solution == ~(\E x \in AllPeople : x \in bank["east"])

====