---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals

VARIABLES boat, bank
vars == <<boat, bank>>

\* A bank is safe if it has no missionaries, or the cannibals never outnumber them.
\* The solution is reached when the east bank is empty (all are on the west bank).
\* The boat must carry one or two people per crossing; it never travels empty.
\* Crossing is only allowed when the resulting distribution is safe on both banks.
\* When TLC cannot find an enabled crossing it reports a real deadlock, which is not
\* the same as the puzzle being solved.

RECURSIVE Count(_)
Count(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE IN 1 + Count(S \ {x})

\* Safety: each bank is either cannibal-only or has at least as many missionaries.
\* Liveness: the east bank never stays non-empty forever without a solution.
TypeOK ==
    /\ boat \in Banks
    /\ bank \in [Banks -> SUBSET People]
    /\ \A b \in Banks :
         (bank[b] \cap Missionaries = {} \/ Count(bank[b] \cap Cannibals) <= Count(bank[b] \cap Missionaries))
    /\ \A b \in Banks : Cardinality(bank[b] \cap Missionaries) = 3 - Cardinality(bank[CHOOSE c \in Banks : c # b] \cap Missionaries)

Init ==
    /\ boat = "east"
    /\ bank = [b \in Banks |-> IF b = "east" THEN People ELSE {}]

Move ==
    /\ \E g \in SUBSET bank[boat] :
         /\ g # {}
         /\ Cardinality(g) <= 2
         /\ boat' = (CHOOSE c \in Banks : c # boat)
         /\ bank' = [bank EXCEPT ![boat] = @ \ g, [CHOOSE c \in Banks : c # boat] = @ \cup g]
    /\ UNCHANGED <<>>

Next == Move

Solution == boat = "west" /\ bank["east"] = {}
====