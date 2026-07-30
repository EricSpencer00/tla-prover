---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boat, bankOf

vars == <<boat, bankOf>>

TypeOK ==
    /\ boat \in Banks
    /\ bankOf \in [People -> Banks]

\* Every bank is either empty of missionaries or has at least as many
\* missionaries as cannibals; a bank occupied only by cannibals is safe.
BankSafe(b) ==
    LET mission == Cardinality({p \in People : bankOf[p] = b /\ p \in Missionaries})
        cannib  == Cardinality({p \in People : bankOf[p] = b /\ p \in Cannibals})
    IN  mission = 0 \/ cannib <= mission

\* The boat must carry one or two people per crossing, never empty.
BoatLoad ==
    Cardinality({p \in People : bankOf[p] = boat})

Init ==
    /\ boat = "east"
    /\ bankOf = [p \in People |-> "east"]

\* The crossing group is implicit: anyone on the departure bank may have
\* moved. The bankOf update swaps their bank, so the group changes together
\* with the boat's location and the safety check.
Next ==
    /\ BoatLoad >= 1 /\ BoatLoad <= 2
    /\ LET dest == IF boat = "east" THEN "west" ELSE "east"
           newBankOf == [p \in People |->
                            IF bankOf[p] = boat THEN dest ELSE bankOf[p]]
       IN  /\ BankSafe(dest)
           /\ BankSafe(boat)
           /\ bankOf' = newBankOf
           /\ boat' = dest
    /\ UNCHANGED <<>>

Solution == \A b \in Banks : BankSafe(b)

Spec == Init /\ [][Next]_vars

====