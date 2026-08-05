---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
Persons == Missionaries \cup Cannibals
StartBank == "east"
OtherBank(b) == IF b = "east" THEN "west" ELSE "east"

VARIABLES bank, occupants

vars == <<bank, occupants>>

\* Safety: a bank is safe if it has no missionaries, or contains at least as
\* many missionaries as cannibals (so the cannibals can never outnumber them).
Safe(b) ==
  LET occ == occupants[b]
      m == occ \cap Missionaries
      c == occ \cap Cannibals
  IN m = {} \/ Cardinality(c) <= Cardinality(m)

TypeOK ==
  /\ bank \in Banks
  /\ occupants \in [Banks -> SUBSET Persons]

Init ==
  /\ bank = StartBank
  /\ occupants = [b \in Banks |-> IF b = StartBank THEN Persons ELSE {}]

\* A crossing never leaves the boat empty, and never takes more than two persons.
Move(S) ==
  /\ S # {}
  /\ Cardinality(S) <= 2
  /\ S \subseteq occupants[bank]
  /\ LET dest == OtherBank(bank)
         occ' == [occupants EXCEPT ![bank] = occupants[bank] \ S, ![dest] = occupants[dest] \cup S]
     IN Safe(bank) /\ Safe(dest)
  /\ occupants' = [occupants EXCEPT ![bank] = occupants[bank] \ S, ![OtherBank(bank)] = occupants[OtherBank(bank)] \cup S]
  /\ bank' = OtherBank(bank)

Next == \E S \in SUBSET Persons : Move(S)

\* Progress: the east bank eventually empties (everyone reaches the west bank).
Solution == <>(occupants[StartBank] = {})

Spec == Init /\ [][Next]_vars /\ SF_vars(Next) /\ WF_vars(Next)

====