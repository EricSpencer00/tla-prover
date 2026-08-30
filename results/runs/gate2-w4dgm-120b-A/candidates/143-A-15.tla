---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

VARIABLES boatAt, bank, solution
vars == <<boatAt, bank, solution>>

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumSet(f, S \ {x})

LoadAt(b) == SumSet([ p \in People |-> IF bank[b][p] THEN 1 ELSE 0 ], People)

TypeOK ==
    /\ boatAt \in Banks
    /\ bank \in [Banks -> SUBSET People]
    /\ solution \in BOOLEAN

Init ==
    /\ boatAt = "east"
    /\ bank = [ b \in Banks |> IF b = "east" THEN People ELSE {} ]
    /\ solution = FALSE

SafeBank ==
    \A b \in Banks :
        LET ms == Cardinality(bank[b] \cap Missionaries)
            cs == Cardinality(bank[b] \cap Cannibals)
        IN ms = 0 \/ cs <= ms

Move ==
    /\ ~solution
    /\ \E S \subseteq bank[boatAt] :
        /\ Cardinality(S) \in 1..2
        /\ \A p \in S : bank' = [bank EXCEPT ![boatAt] = @ \ {p}, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \cup {p}]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
    /\ solution' = (LoadSet("east") = 0)
    /\ SafeBank

Next == Move

Spec == Init /\ [][Next]_vars

Solution == solution

====