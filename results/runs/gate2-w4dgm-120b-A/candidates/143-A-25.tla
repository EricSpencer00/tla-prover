---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES boatAt, people, record

vars == <<boatAt, people, record>>

TypeOK ==
    /\ boatAt \in Banks
    /\ people \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
    /\ record \in Seq([by: Banks, group: SUBSET (Missionaries \cup Cannibals)])

Init ==
    /\ boatAt = "east"
    /\ people = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]
    /\ record = <<>>

BankSafe(b) ==
    LET m == Cardinality({x \in people[b] : x \in Missionaries})
        c == Cardinality({x \in people[b] : x \in Cannibals})
    IN (m = 0) \/ (c <= m)

Move ==
    \E g \in SUBSET (Missionaries \cup Cannibals) :
        /\ g # {}
        /\ Cardinality(g) <= 2
        /\ g \subseteq people[boatAt]
        /\ /\ \A b \in Banks : Cardinality({x \in people[b] : x \in Missionaries}) >= Cardinality({x \in people[b] : x \in Cannibals}) \/ Cardinality({x \in people[b] : x \in Missionaries}) = 0
        /\ LET newPeople == [people EXCEPT ![boatAt] = people[boatAt] \ g,
                                          ![IF boatAt = "east" THEN "west" ELSE "east"] = people[IF boatAt = "east" THEN "west" ELSE "east"] \cup g]
           IN \A b \in Banks : LET m == Cardinality({x \in newPeople[b] : x \in Missionaries})
                                   c == Cardinality({x \in newPeople[b] : x \in Cannibals})
                               IN (m = 0) \/ (c <= m)
        /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
        /\ people' = [people EXCEPT ![boatAt] = people[boatAt] \ g,
                                ![IF boatAt = "east" THEN "west" ELSE "east"] = people[IF boatAt = "east" THEN "west" ELSE "east"] \cup g]
        /\ record' = Append(record, [by |-> boatAt, group |-> g])

Next == Move

Solution == \A b \in Banks : Cardinality({x \in people[b] : x \in Missionaries}) >= Cardinality({x \in people[b] : x \in Cannibals}) \/ Cardinality({x \in people[b] : x \in Missionaries}) = 0

Spec == Init /\ [][Next]_vars

====