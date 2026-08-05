---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

\* The classic missionaries and cannibals puzzle: three missionaries and three cannibals
\* must cross a river using a boat that carries at most two people. On a bank with
\* missionaries present, cannibals must never outnumber them (or the missionaries are
\* eaten). The boat cannot cross empty.
CONSTANTS Missionaries, Cannibals
People == Missionaries \cup Cannibals

VARIABLES bank, boatAt
vars == <<bank, boatAt>>

Banks == {"east", "west"}

\* Church-Rosser-style reachability: a bank is safe if it has no missionaries, or
\* if missionaries are present they are not outnumbered by cannibals.
TypeOK ==
  /\ bank \in [Banks -> SUBSET People]
  /\ boatAt \in Banks

BankSafe(b) ==
  LET m == Cardinality(bank[b] \cap Missionaries)
      c == Cardinality(bank[b] \cap Cannibals)
  IN m = 0 \/ c <= m

Init ==
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ boatAt = "east"

\* A crossing moves one or two people from the current bank to the other, landing
\* in a safe configuration on both banks.
Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ g \subseteq bank[boatAt]
  /\ LET other == IF boatAt = "east" THEN "west" ELSE "east"
         newBank ==
           [b \in Banks |->
             IF b = boatAt THEN bank[b] \ g ELSE bank[b] \cup g]
         safe == BankSafe(other) /\ BankSafe(boatAt)
     IN safe /\ bank' = newBank /\ boatAt' = other)

Next == \E g \in SUBSET People : Move(g)

\* Every reachable state is safe on both banks.
Solution == \A b \in Banks : BankSafe(b)
====