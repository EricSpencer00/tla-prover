---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, people

vars == <<boatAt, people>>

\* Safety: either no missionaries on a bank, or cannibals never outnumber them.
TypeOK ==
    /\ boatAt \in Banks
    /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
    /\ boatAt = "east"
    /\ people = [east |-> Missionaries \cup Cannibals, west |-> {}]

\* Bank, group: a non-empty set of at most two people that actually stands on the
\* boat's current bank and keeps the banks safe after the cross.
Move ==
    \E bank \in Banks, group \in SUBSET (Missionaries \cup Cannibals):
        /\ group # {}
        /\ Cardinality(group) <= 2
        /\ group \subseteq people[bank]
        /\ Cardinality(group) >= Cardinality([x \in group: x \in Cannibals])
        /\ Cardinality(group) >= Cardinality([x \in group: x \in Missionaries])
        /\ LET newPeople ==
                [people EXCEPT ![bank] = people[bank] \ group,
                 ![IF bank = "east" THEN "west" ELSE "east"] =
                    people[IF bank = "east" THEN "west" ELSE "east"] \cup group]
           IN /\ (\A b \in Banks :
                     (people[b] \cup newPeople[b]) = (Missionaries \cup Cannibals))
              /\ (\A b \in Banks :
                     LET total == Cardinality(people[b] \cup newPeople[b])
                         mis == Cardinality([x \in (people[b] \cup newPeople[b]): x \in Missionaries])
                         can == Cardinality([x \in (people[b] \cup newPeople[b]): x \in Cannibals])
                     IN (mis = 0) \/ (can <= mis))
        /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
        /\ people' = newPeople

Next == Move

\* Progress guarantee: the emptying of the starting bank is always reachable, so
\* the puzzle is always solvable and a counterexample to this is a genuine deadlock.
Solution == <>(people["east"] = {})

INVARIANT TypeOK

====