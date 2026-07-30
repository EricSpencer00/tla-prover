---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals
Banks == {"east", "west"}

VARIABLES boatBank, bankPeople

vars == <<boatBank, bankPeople>>

OnBank(b, k) == { p \in People : bankPeople[b][p] = k }

TypeOK ==
    /\ boatBank \in Banks
    /\ bankPeople \in [Banks -> [People -> {"east", "west"}]]
    /\ Cardinality(bankPeople["east"]) = 6
    /\ Cardinality(bankPeople["west"]) = 0

\* A bank is safe if it holds no missionaries, or cannibals do not outnumber
\* missionaries there (the puzzle's outnumbering rule, or a cannibal-only bank).
BankSafe(b) ==
    LET ms == Cardinality(OnBank(b, "missionary"))
        cs == Cardinality(OnBank(b, "cannibal"))
    IN ms = 0 \/ cs <= ms

Solution ==
    /\ TypeOK
    /\ \A b \in Banks : BankSafe(b)
    /\ Cardinality(bankPeople[boatBank]) \in {1, 2}

\* Count of missionaries (or cannibals) currently on the boat, i.e. away from
\* both banks, derived from the people left on bankPeople.
Aboard(m) ==
    Cardinality({ p \in Missionaries : bankPeople["west"][p] = "west" })
        + Cardinality({ p \in Missionaries : bankPeople["east"][p] = "east" })
        + Cardinality({ p \in Cannibals : bankPeople["west"][p] = "west" })
        + Cardinality({ p \in Cannibals : bankPeople["east"][p] = "east" })
        - 6

Init ==
    /\ boatBank = "east"
    /\ bankPeople = [b \in Banks |-> [p \in People |-> IF b = "east" THEN "east" ELSE "west"]]

\* Move: the boat carries one or two people from its current bank to the other,
\* never landing on a bank that would be unsafe.
Next ==
    \/ \E g \in SUBSET People :
        /\ g # {}
        /\ Cardinality(g) \in {1, 2}
        /\ \A p \in g : bankPeople[boatBank][p] = boatBank
        /\ Cardinality(OnBank({"east", "west"}[boatBank], "missionary")) = 3
        /\ LET newBank == {"east", "west"}[boatBank]
               np == [q \in People |-> IF q \in g THEN newBank ELSE bankPeople[boatBank][q]]
               nb == [q \in People |-> IF q \in g THEN boatBank ELSE bankPeople[newBank][q]]
           IN /\ bankPeople' = [boatBank |-> np, newBank |-> nb]
              /\ boatBank' = newBank
              /\ Aboard(g) \in {1, 2}
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

====