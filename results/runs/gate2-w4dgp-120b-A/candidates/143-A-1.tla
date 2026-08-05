---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

\* Classic missionaries and cannibals puzzle: a boat ferrying three missionaries and
\* three cannibals across a river.  The safety condition is that on any bank
\* containing missionaries, cannibals must never outnumber them (else the
\* missionaries are eaten).  The boat never crosses empty and never carries more
\* than its capacity of two.

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
Origin(b) == IF b = "east" THEN "west" ELSE "east"

VARIABLES boatBank, bankPeople

vars == <<boatBank, bankPeople>>

TypeOK ==
    /\ boatBank \in Banks
    /\ bankPeople \in [Banks -> SUBSET People]

Init ==
    /\ boatBank = "east"
    /\ bankPeople = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

\* A move is safe when, after the crossing, every bank either has no
\* missionaries or has at least as many missionaries as cannibals.
Safe(bank) ==
    LET M == Cardinality(bankPeople[bank] \cap Missionaries)
        C == Cardinality(bankPeople[bank] \cap Cannibals)
    IN (M = 0) \/ (C <= M)

Move(S) ==
    /\ S # {}
    /\ Cardinality(S) <= 2
    /\ S \subseteq bankPeople[boatBank]
    /\ LET newPeople == [bankPeople EXCEPT ![boatBank] = @ \ S, ![Origin(boatBank)] = @ \cup S]
       IN /\ Safe(boatBank)
          /\ Safe(Origin(boatBank))
          /\ bankPeople' = newPeople
    /\ boatBank' = Origin(boatBank)

Next == \E S \in SUBSET People : Move(S)

\* The safety invariant is the outnumbering condition applied to both banks.
TypeOK /\ \A b \in Banks : Safe(b)

Solution == bankPeople["east"] = {}
====