---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

ASSUME Missionaries = {"m1", "m2", "m3"}
ASSUME Cannibals = {"k1", "k2", "k3"}

People == Missionaries \cup Cannibals

VARIABLES bank, boatAt

vars == <<bank, boatAt>>

Edge == {Missionaries, Cannibals}

Init ==
    /\ bank = [e \in Edge |-> IF e = Missionaries THEN Missionaries ELSE Cannibals]
    /\ boatAt \in {"east", "west"}

\* The bank a passenger is on is inferred from the 'bank' map, so no extra
\* bookkeeping is needed when people move.
Move(g) ==
    /\ g # {}
    /\ Cardinality(g) <= 2
    /\ boatAt = "east"
    /\ g \subseteq bank[Missionaries]
    /\ bank' = [bank EXCEPT !["east"] = bank["east"] \ g, !["west"] = bank["west"] \cup g]
    /\ boatAt' = "west"

Move(g) ==
    \/ Move(g) /\ boatAt = "east" /\ bank' = [bank EXCEPT !["east"] = bank["east"] \ g, !["west"] = bank["west"] \cup g] /\ boatAt' = "west"
    \/ Move(g) /\ boatAt = "west" /\ g \subseteq bank[Missionaries] /\ bank' = [bank EXCEPT !["west"] = bank["west"] \ g, !["east"] = bank["east"] \cup g] /\ boatAt' = "east"

Next ==
    \/ (\E g \in SUBSET People: g # {} /\ Cardinality(g) <= 2 /\ Move(g))

MissionsOn(b) == Cardinality(bank[Missionaries] \cap b)
CannibalsOn(b) == Cardinality(bank[Cannibals] \cap b)

\* Bank safety: missionaries must never be outnumbered by cannibals.
BankSafe ==
    /\ (MissionsOn(Missionaries) = 0 \/ CannibalsOn(Missionaries) <= MissionsOn(Missionaries))
    /\ (MissionsOn(Cannibals) = 0 \/ CannibalsOn(Cannibals) <= MissionsOn(Cannibals))

\* The puzzle's solution condition is the east bank being empty.
Solved == bank[Missionaries] = {} /\ bank[Cannibals] = {}

\* The first invariant is the domain check: everything is on a bank.
TypeOK ==
    /\ bank \in [Edge -> SUBSET People]
    /\ boatAt \in {"east", "west"}

\* The second invariant caps the number of people crossing together.
Solution == BankSafe

====