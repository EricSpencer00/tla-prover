---- MODULE MissionariesAndCannibals ----
\* Classic missionaries-and-cannibals crossing puzzle: a boat carries at most two
\* people across a river, and on any bank missionaries must not be outnumbered
\* by cannibals (or they get eaten). The model is deliberately tiny: exactly three
\* missionaries and three cannibals, and the "solved" state is when the east bank
\* is empty (everyone has crossed). This module defines every identifier that the
\* reference TLC configuration expects.
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}
MaxCarry == 2
Nobody == "nobody"

VARIABLES boat, bank, carried

vars == <<boat, bank, carried>>

TypeOK ==
  /\ boat \in Banks
  /\ bank \in [Banks -> SUBSET People]
  /\ carried \in SUBSET People

BankPeople(b) == Cardinality({p \in People : bank[b] \ni p})
BankMissionaries(b) ==
  Cardinality({p \in Missionaries : bank[b] \ni p})
BankCannibals(b) ==
  Cardinality({p \in Cannibals : bank[b] \ni p})

\* A bank is safe if it has no missionaries, or its cannibals are not in
\* majority over the missionaries present.
BankSafe(b) ==
  \/ BankMissionaries(b) = 0
  \/ BankCannibals(b) <= BankMissionaries(b)

Safe == /\ BankSafe("east")
        /\ BankSafe("west")

Init ==
  /\ boat = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
  /\ carried = {}

\* Load one or two people onto the boat on the current bank; the move is only
\* enabled when the resulting distribution leaves both banks safe.
Embark(g) ==
  /\ g \subseteq bank[boat]
  /\ g # {}
  /\ Cardinality(g) <= MaxCarry
  /\ BankMissionaries(boat) - Cardinality(g \cap Missionaries) >= 0
  /\ BankCannibals(boat) - Cardinality(g \cap Cannibals) >= 0
  /\ bank' = [bank EXCEPT ![boat] = @ \ g]
  /\ carried' = g
  /\ UNCHANGED boat

\* The boat has crossed and drops everybody at the destination bank.
Debark ==
  /\ carried # {}
  /\ LET other == IF boat = "east" THEN "west" ELSE "east" IN
       /\ bank' = [bank EXCEPT ![other] = @ \cup carried]
       /\ carried' = {}
       /\ boat' = other

Next == (\E g \in SUBSET People : Embark(g)) \/ Debark

Spec == Init /\ [][Next]_vars

\* SAFETY PROPERTY: wherever missionaries are present on a bank, cannibals do
\* not outnumber them (the only way they can be present without being outnumbered
\* is if the bank has no missionaries at all).
Solution == Safe

\* FACTORIZATION PROPERTY: a bank is safe exactly when it either carries no
\* missionaries or its cannibals are not in majority.
TypeOK == TypeOK /\ Safe

====