---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boat, people

vars == <<boat, people>>

TypeOK ==
  /\ boat \in Banks
  /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

\* Safety: missionaries are never outnumbered on a bank where they are present.
\* If a bank has no missionaries it is trivially safe (only cannibals remain).
BankSafe(b) ==
  \/ (people[b] \cap Missionaries = {})
  \/ Cardinality((people[b] \cap Missionaries) \cup (people[b] \cap Cannibals))
       >= Cardinality(people[b] \cap Cannibals)

\* The boat always carries at least one person and at most two.
BoatLoadValid(c) == Cardinality(c) \in {1, 2}

\* The move is a genuine crossing: the boarded set moves the boat to the other bank,
\* and the resulting banks must both still be safe.
Move(b, c) ==
  /\ boat = b
  /\ c \subseteq people[b]
  /\ BoatLoadValid(c)
  /\ \A d \in Banks : BankSafe(d)
  /\ people' = [people EXCEPT ![b] = @ \ c, ![Destination(b)] = @ \cup c]
  /\ boat' = Destination(b)
  /\ UNCHANGED <<>>

Destination(b) == IF b = "east" THEN "west" ELSE "east"

Next ==
  \/ Move("east", {})
  \/ Move("west", {})
  \/ \E c \in SUBSET (Missionaries \cup Cannibals) : Move("east", c)
  \/ \E c \in SUBSET (Missionaries \cup Cannibals) : Move("west", c)

Init ==
  /\ boat = "east"
  /\ people = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

Solution == \A b \in Banks : BankSafe(b)

Spec == Init /\ [][Next]_vars

====