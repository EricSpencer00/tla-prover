---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* The boat never travels empty and never carries more than two people.
\* Goal: everyone moves from the east bank to the west bank without ever
\* leaving missionaries outnumbered on either bank.
Banks == {"east", "west"}
AllPeople == Missionaries \cup Cannibals

VARIABLES boat, people
vars == <<boat, people>>

TypeOK ==
  /\ boat \in Banks
  /\ people \in [Banks -> SUBSET AllPeople]

Init ==
  /\ boat = "east"
  /\ people = [b \in Banks |-> IF b = "east" THEN AllPeople ELSE {}]

\* A move is safe iff both banks stay safe after everyone on board disembarks.
Moved(a) == people[boat] \ (a \cup people[boat])
Arrived(b) == people[boat] \cup a
Cross(a) == Moved(a) \cup [boat |-> IF boat = "east" THEN "west" ELSE "east"]

\* The boat carries one or two people; never empty, never overloaded.
\* Both banks must remain safe afterwards.
Move(a) ==
  /\ a # {}
  /\ Cardinality(a) <= 2
  /\ people[boat] \cap a = {}
  /\ LET m == Moved(a), a2 == Arrived(a) IN
       /\ /\ (m["east"] = {} \/ Cardinality(m["cannibals"] \cup m["missionaries"]) >= Cardinality(m["missionaries"]))
          /\ (m["west"] = {} \/ Cardinality(m["cannibals"] \cup m["missionaries"]) >= Cardinality(m["missionaries"]))
          /\ (a2["east"] = {} \/ Cardinality(a2["cannibals"] \cup a2["missionaries"]) >= Cardinality(a2["missionaries"]))
          /\ (a2["west"] = {} \/ Cardinality(a2["cannibals"] \cup a2["missionaries"]) >= Cardinality(a2["missionaries"]))
  /\ people' = Cross(a)
  /\ UNCHANGED boat

Next == \E a \in SUBSET AllPeople : Move(a)

\* Progress: the east bank is eventually emptied (everyone reaches the west bank).
Solution == <>(people["east"] = {})
====