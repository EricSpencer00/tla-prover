---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

\* Boat location is a location name; People is the set of all individuals; Banks
\* maps a location name to the set of people standing on that bank.
VARIABLES BoatAt, People, Banks

vars == <<BoatAt, People, Banks>>

TypeOK ==
    /\ BoatAt \in {"east", "west"}
    /\ People = Missionaries \union Cannibals
    /\ Banks \in [ {"east", "west"} -> SUBSET People ]

Init ==
    /\ BoatAt = "east"
    /\ People = Missionaries \union Cannibals
    /\ Banks = [ loc \in {"east", "west"} |-> IF loc = "east" THEN People ELSE {} ]

MissionariesAt(loc) == Banks[loc] \intersect Missionaries
CannibalsAt(loc)    == Banks[loc] \intersect Cannibals

BankSafe(loc) ==
    \/ MissionariesAt(loc) = {}
    \/ Cardinality(CannibalsAt(loc)) <= Cardinality(MissionariesAt(loc))

Move(group) ==
    /\ group \subseteq People
    /\ 1 <= Cardinality(group) <= 2
    /\ group \subseteq Banks[BoatAt]
    /\ BankSafe(BoatAt)
    /\ LET dest == IF BoatAt = "east" THEN "west" ELSE "east" IN
       /\ Banks' = [ Banks EXCEPT ![BoatAt] = @ \ group, ![dest] = @ \union group ]
       /\ BoatAt' = dest
    /\ UNCHANGED People

Next == \E group \in SUBSET People : Move(group)

Solution == \A loc \in {"east", "west"} : BankSafe(loc)

Spec == Init /\ [][Next]_vars

====