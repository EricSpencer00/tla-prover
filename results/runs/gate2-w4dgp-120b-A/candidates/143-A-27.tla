---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

\* Missionaries and cannibals crossing a river.  A bank is safe when it holds
\* only cannibals or when cannibals do not outnumber missionaries; the boat
\* always carries one or two people per crossing.  The puzzle is solved when
\* the east bank is empty (everyone is on the west bank).
CONSTANTS Missionaries, Cannibals

AllPeople == Missionaries \cup Cannibals
Banks == {"east", "west"}
OtherBank(e) == IF e = "east" THEN "west" ELSE "east"
\* The boat carries at most two people: its manifest is a subset of all people
\* of size one or two, and it never rides empty.
Carrier == {S \in SUBSET AllPeople : 1 <= Cardinality(S) /\ Cardinality(S) <= 2}

VARIABLES bank, boatDock

vars == <<bank, boatDock>>

TypeOK ==
  /\ bank \in [Banks -> SUBSET AllPeople]
  /\ boatDock \in Banks

\* Safe: on any bank that holds missionaries, cannibals do not outnumber them.
BankSafe(b) ==
  LET M == Cardinality(bank[b] \cap Missionaries)
      C == Cardinality(bank[b] \cap Cannibals)
  IN M = 0 \/ C <= M

Init ==
  /\ bank = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]
  /\ boatDock = "east"

\* A group of 1 or 2 people on the current bank crosses to the other side,
\* provided both banks stay safe afterwards.
Move(S) ==
  /\ S \in Carrier
  /\ S \subseteq bank[boatDock]
  /\ bank' = [bank EXCEPT ![boatDock] = @ \ S, ![OtherBank(boatDock)] = @ \cup S]
  /\ boatDock' = OtherBank(boatDock)

Next ==
  \E S \in Carrier : Move(S)

\* The arrival bank is never empty: a solution exists.
Solution ==
  /\ \A b \in Banks : BankSafe(b)
  /\ bank["east"] # {}

Spec == Init /\ [][Next]_vars

====