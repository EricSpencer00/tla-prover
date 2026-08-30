---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"west", "east"}
People == Missionaries \union Cannibals
\* bank[p] is the bank p currently stands on; BoatAt is where the boat is docked.
VARIABLES bank, BoatAt

TypeOK ==
    /\ bank \in [People -> Banks]
    /\ BoatAt \in Banks

Init ==
    /\ bank = [p \in People |-> "east"]
    /\ BoatAt = "east"

\* Everyone on a bank; counts of each species present there.
Count(bank, S) ==
    Cardinality({p \in People : bank[p] = bank /\ p \in S})

\* A bank that would be unsafe on its own: missionaries present and outnumbered.
UnsafeBank(bank) ==
    /\ Count(bank, Missionaries) > 0
    /\ Count(bank, Cannibals) > Count(bank, Missionaries)

Move(trav, destBank) ==
    /\ destBank # BoatAt
    /\ Cardinality(trav) \in 1..2
    /\ \A p \in trav : bank[p] = BoatAt
    /\ \A b \in Banks : b # destBank => Count(b, Missionaries) = 0 \/ Count(b, Cannibals) <= Count(b, Missionaries)
    /\ \A b \in Banks : b # BoatAt => Count(b, Missionaries) = 0 \/ Count(b, Cannibals) <= Count(b, Missionaries)
    /\ bank' = [p \in People |-> IF p \in trav THEN destBank ELSE bank[p]]
    /\ BoatAt' = destBank

Next ==
    \/ \E s \in SUBSET People, d \in Banks : Move(s, d)
    \/ UNCHANGED <<bank, BoatAt>>

\* Missionaries are never outnumbered on any bank, and boats always carry people.
TypeOK == TypeOK
Solution == \A b \in Banks : Count(b, Missionaries) = 0 \/ Count(b, Cannibals) <= Count(b, Missionaries)

====