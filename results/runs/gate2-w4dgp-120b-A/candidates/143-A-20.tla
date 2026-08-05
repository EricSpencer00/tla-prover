---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

BALANCE == Missionaries \cup Cannibals

VARIABLES dock, banks
vars == <<dock, banks>>

RECURSIVE CountBank(_, _)
CountBank(S, left) == IF left = {} THEN 0
                      ELSE LET x == CHOOSE y \in left : TRUE
                           IN (IF x \in S THEN 1 ELSE 0) + CountBank(S, left \ {x})

SAFE(bk) == LET m == CountBank(Missionaries, bk)
                c == CountBank(Cannibals, bk)
            IN m = 0 \/ c <= m

TypeOK ==
    /\ dock \in {"east", "west"}
    /\ banks \in [BALANCE -> {"east", "west"}]

Init ==
    /\ dock = "east"
    /\ banks = [p \in BALANCE |-> "east"]

Move ==
    /\ \E g \subseteq (BALANCE \ {p \in BALANCE : banks[p] = dock}),
         g # {}, Cardinality(g) <= 2
        /\ SAFE({p \in BALANCE : ((banks[p] = dock) /\ (p \notin g)) \/ (banks[p] = (IF dock = "east" THEN "west" ELSE "east"))})
        /\ banks' = [p \in BALANCE |->
                        IF p \in g THEN (IF dock = "east" THEN "west" ELSE "east") ELSE banks[p]]
        /\ dock' = IF dock = "east" THEN "west" ELSE "east"
    /\ TRUE

Next == Move

TypeOKInv == TypeOK

InitialBankSafe == SAFE({p \in BALANCE : banks[p] = "east"}) /\ SAFE({p \in BALANCE : banks[p] = "west"})

Goal == {p \in BALANCE : banks[p] = "east"} = {}
====