---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES bank, boatDock, atBank

vars == <<bank, boatDock, atBank>>

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
\* A bank is safe if it holds no missionaries or the cannibals there do not
\* outnumber the missionaries that same bank holds.
BankSafe(b) == (bank[b] \cap Missionaries = {}) \/ (Cardinality(bank[b] \cap Cannibals) <= Cardinality(bank[b] \cap Missionaries))

TypeOK ==
    /\ bank \in [Banks -> SUBSET People]
    /\ boatDock \in Banks
    /\ atBank \in [People -> Banks]
    /\ bank["east"] \cup bank["west"] = People
    /\ bank["east"] \cap bank["west"] = {}

Init ==
    /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ boatDock = "east"
    /\ atBank = [p \in People |-> "east"]

\* Move a group of size one or two across the river in the boat, only if the
\* resulting distribution is safe on both banks.
Next ==
    /\ boatDock' = IF boatDock = "east" THEN "west" ELSE "east"
    /\ \E g \in SUBSET bank[boatDock] :
         /\ Cardinality(g) \in {1, 2}
         /\ (bank[boatDock] \ g) \cup g /= {}
         /\ BankSafe(boatDock)
         /\ BankSafe(IF boatDock = "east" THEN "west" ELSE "east")
         /\ bank' = [bank EXCEPT ![boatDock] = @ \ g, ![IF boatDock = "east" THEN "west" ELSE "east"] = @ \cup g]
         /\ atBank' = [p \in People |-> IF p \in g THEN (IF boatDock = "east" THEN "west" ELSE "east") ELSE atBank[p]]
    /\ UNCHANGED <<>>

Next == Next

Solution == bank["east"] = {}

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Spec)

TypeOK == TypeOK

Solution == Solution

====