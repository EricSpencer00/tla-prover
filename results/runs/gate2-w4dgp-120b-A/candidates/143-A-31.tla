---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
AllPeople == Missionaries \cup Cannibals
Opposite(b) == IF b = "east" THEN "west" ELSE "east"
Count(p, S) == Cardinality({x \in S : x = p})

VARIABLES boatBank, bankPeople

vars == <<boatBank, bankPeople>>

TypeOK ==
  /\ boatBank \in Banks
  /\ bankPeople \in [Banks -> SUBSET AllPeople]

Init ==
  /\ boatBank = "east"
  /\ bankPeople = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]

BankSafe(b) ==
  \/ bankPeople[b] \cap Missionaries = {}
  \/ Count("cannibals", bankPeople[b]) <= Count("missionaries", bankPeople[b])

BankSafeForAll == \A b \in Banks : BankSafe(b)

Move(g) ==
  /\ g # {}
  /\ Cardinality(g) <= 2
  /\ g \subseteq bankPeople[boatBank]
  /\ LET
        newBank == [bankPeople EXCEPT ![boatBank] = bankPeople[boatBank] \ g, ![Opposite(boatBank)] = bankPeople[Opposite(boatBank)] \cup g]
     IN /\ BankSafe(newBank["east"])
        /\ BankSafe(newBank["west"])
        /\ bankPeople' = newBank
  /\ boatBank' = Opposite(boatBank)

Next == \E g \in SUBSET AllPeople: Move(g)

Solution == \A b \in Banks : BankSafe(b)
Goal == bankPeople["east"] = {}

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Goal

====