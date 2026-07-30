---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

VARIABLES dock, people
vars == <<dock, people>>

RECURSIVE Count(_, _)
Count(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + Count(f, S \ {x})

TypeOK ==
    /\ dock \in Banks
    /\ people \in [Banks -> SUBSET (Missionaries \union Cannibals)]

Init ==
    /\ dock = "east"
    /\ people = [b \in Banks |-> IF b = "east" THEN Missionaries \union Cannibals ELSE {}]

SafeBank(b) ==
    LET ms == {x \in people[b] : x \in Missionaries}
        cs == {x \in people[b] : x \in Cannibals}
    IN \/ ms = {}
        \/ Cardinality(cs) <= Cardinality(ms)

Solution ==
    /\ SafeBank("east")
    /\ SafeBank("west")
    /\ dock \in Banks
    /\ \A b \in Banks : people[b] \subseteq Missionaries \union Cannibals

Move == \E group \in SUBSET (Missionaries \union Cannibals) :
    /\ group # {}
    /\ Cardinality(group) <= 2
    /\ group \subseteq people[dock]
    /\ LET newEast == IF dock = "east" THEN people["east"] \ group ELSE people["east"] \cup group
           newWest == IF dock = "west" THEN people["west"] \ group ELSE people["west"] \cup group
       IN /\ SafeBank("east") => SafeBank("west")
          /\ SafeBank("west") => SafeBank("east")
          /\ people' = [ "east" |-> newEast, "west" |-> newWest ]
    /\ dock' = (IF dock = "east" THEN "west" ELSE "east")

Next == Move

Spec == Init /\ [][Next]_vars

====