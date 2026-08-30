---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences

CONSTANTS Missionaries, Cannibals

VARIABLES boatAt, bank, moving

vars == <<boatAt, bank, moving>>

Banks == {"east", "west"}
Persons == Missionaries \cup Cannibals

Init ==
  /\ boatAt = "east"
  /\ bank = [b \in Banks |-> IF b = "east" THEN Persons ELSE {}]
  /\ moving = {}

TypeOK ==
  /\ boatAt \in Banks
  /\ bank \in [Banks -> SUBSET Persons]
  /\ moving \subseteq Persons

SafeBank(b) ==
  \/ (Missionaries \cap bank[b] = {})
  \/ (Cardinality(Cannibals \cap bank[b]) <= Cardinality(Missionaries \cap bank[b]))

\* The boat is the empty set when no crossing is in progress.
Safe ==
  /\ SafeBank("east")
  /\ SafeBank("west")
  /\ moving # {}
  /\ Cardinality(moving) <= 2

Move ==
  /\ moving = {}
  /\ \E group \in SUBSET bank[boatAt] :
       /\ group # {}
       /\ Cardinality(group) <= 2
       /\ moving' = group
  /\ boatAt' = boatAt
  /\ bank' = [bank EXCEPT ![boatAt] = @ \ group]

\* Completion is the moment the persons actually change banks.
Complete ==
  /\ moving # {}
  /\ bank' = [b \in Banks |->
                IF b = boatAt THEN bank[b] \ moving
                ELSE IF b = (IF boatAt = "east" THEN "west" ELSE "east") THEN bank[b] \cup moving
                ELSE bank[b]]
  /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
  /\ moving' = {}

Next ==
  \/ Move
  \/ Complete

\* Progress is only claimed when the species ratio can not be re-established,
\* i.e. when everybody has actually arrived on the far bank.
Solution == boatAt = "west" /\ bank["west"] = Persons

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Complete)

\* No missionaries outnumbered by cannibals, and the boat is never empty.
Invariant ==
  /\ SafeBank("east")
  /\ SafeBank("west")
  /\ moving # {}

====