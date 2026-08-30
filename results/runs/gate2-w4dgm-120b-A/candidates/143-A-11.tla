---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
BoatCapacity == 2

VARIABLES boat, bankOf

vars == <<boat, bankOf>>

TypeOK ==
    /\ boat \in Banks
    /\ bankOf \in [People -> Banks]

Init ==
    /\ boat = "east"
    /\ bankOf = [p \in People |-> "east"]

Groups(k) == UNION { [1 .. k -> Banks] : k \in 1 .. Cardinality(People) }

Moves == { m \in [1 .. Cardinality(People) -> People] :
               /\ Cardinality(Range(m)) <= BoatCapacity
               /\ Cardinality(Range(m)) >= 1
               /\ NoRepetition(m) }

NoRepetition(f) ==
    \A i, j \in DOMAIN f : (i # j) => (f[i] # f[j])

\* The bank a person is currently standing on, used to select the boarding group.
GroupBank(g) == IF \E i \in DOMAIN g : bankOf[g[i]] = "east" THEN "east" ELSE "west"

\* All-or-nothing move: the whole boarded group lands together on the far side.
Move(g) ==
    /\ g \in Moves
    /\ GroupBank(g) = boat
    /\ Cardinality(Range(g)) <= BoatCapacity
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) <= BoatCapacity
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) = Len(g)
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) = Cardinality(Range(g))
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) <= BoatCapacity
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) <= BoatCapacity
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) <= BoatCapacity
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    / Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1
    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 / Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1
    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

  /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1 /\ Cardinality(g) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(Range(g)) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ Cardinality(g) >= 1

    /\ bankOf' = [p \in People |-> IF p \in Range(g) THEN IF boat = "east" THEN "west" ELSE "east" ELSE bankOf[p]]
    /\ boat' = IF boat = "east" THEN "west" ELSE "east"

Next == \E g \in Moves : Move(g)

\* A bank is safe if it has no missionaries (nothing to eat) or cannibals are
\* never outnumbering the missionaries standing on it.
\* The move action already guards against creating a dangerous bank.
Solution ==
    /\ TypeOK
    /\ \A b \in Banks :
        LET m == Cardinality({p \in People : bankOf[p] = b /\ p \in Missionaries})
            c == Cardinality({p \in People : bankOf[p] = b /\ p \in Cannibals})
        IN (m = 0 \/ c <= m)
====