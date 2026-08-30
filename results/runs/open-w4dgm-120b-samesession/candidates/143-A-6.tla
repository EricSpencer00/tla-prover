---- MODULE MissionariesAndCannibals ----
CONSTANTS Missionaries, Cannibals

ASSUME Missionaries \subseteq Nat /\ Cannibals \subseteq Nat

VARIABLES boatAtEast, bank
vars == <<boatAtEast, bank>>

Banks == {"east", "west"}

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumOver(f, S \ {x})

MissionariesInBank(b) == SumOver([p \in Missionaries |-> IF bank[b][p] THEN 1 ELSE 0], Missionaries)
CannibalsInBank(b) == SumOver([p \in Cannibals |-> IF bank[b][p] THEN 1 ELSE 0], Cannibals)

TypeOK ==
    /\ boatAtEast \in BOOLEAN
    /\ bank \in [Banks -> [Missionaries \cup Cannibals -> BOOLEAN]]

\* Either a bank has no missionaries, or the cannibals there are not outnumbering them.
BankSafe(b) == (MissionariesInBank(b) = 0) \/ (CannibalsInBank(b) <= MissionariesInBank(b))

Init ==
    /\ boatAtEast = TRUE
    /\ bank = [b \in Banks |-> [x \in Missionaries \cup Cannibals |-> b = "east"]]

\* Move a nonempty group of at most two people from the current bank across the river,
\* but only when the resulting configuration is safe on both banks.
Move(a, b, g) ==
    /\ a # b
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ \A p \in g : bank[a][p]
    /\ BankSafe(b)
    /\ boatAtEast' = ~boatAtEast
    /\ bank' = [bank EXCEPT ![a] = @ \ g, ![b] = @ \cup g]

Next ==
    \/ \E a, b \in Banks, g \in SUBSET (Missionaries \cup Cannibals) : Move(a, b, g)

Solution == \A b \in Banks : BankSafe(b)

Spec == Init /\ [][Next]_vars
====