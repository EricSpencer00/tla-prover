---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatAtEast, bank
vars == <<boatAtEast, bank>>

Banks == {"east", "west"}
AllPeople == Missionaries \cup Cannibals

BankOf(p) == IF p \in Missionaries THEN "missionary" ELSE "cannibal"
Count(S, kind) == Cardinality({p \in S : BankOf(p) = kind})

Init ==
    /\ boatAtEast = TRUE
    /\ bank = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]

\* A move is only enabled when the resulting configuration keeps both banks safe
\* (missionaries never outnumbered by cannibals) and the boat is never sent empty.
Move(g, s) ==
    /\ s \in Banks
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ g \subseteq bank[s]
    /\ Count(bank[If s = "east" Then "west" Else "east"], "cannibal") + Count(g, "cannibal")
       <=
       Count(bank[If s = "east" Then "west" Else "east"], "missionary") + Count(g, "missionary")
    /\ Count(bank[s], "cannibal") - Count(g, "cannibal")
        <= Count(bank[s], "missionary") - Count(g, "missionary")
    /\ bank' = [bank EXCEPT ![s] = @ \ g, ![If s = "east" Then "west" Else "east"] = @ \cup g]
    /\ boatAtEast' = ~boatAtEast

Next ==
    \/ \E s \in Banks, g \in SUBSET AllPeople : Move(g, s)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ boatAtEast \in BOOLEAN
    /\ bank \in [Banks -> SUBSET AllPeople]

\* Safety: no missionaries are ever outnumbered by cannibals on any bank.
SafeCrossing ==
    \A b \in Banks :
        Count(bank[b], "missionary") = 0 \/ Count(bank[b], "cannibal") <= Count(bank[b], "missionary")

\* Progress: the east bank eventually empties (everyone reaches the west bank).
Solution == <>(bank["east"] = {})

====