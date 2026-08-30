---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}

\* The boat carries exactly one or two people per crossing and never travels empty.
BoatCap == 2
MinLoad == 1

VARIABLES dock, occupants

vars == <<dock, occupants>>

\* occupants[b] is the set of Missionaries and Cannibals currently standing on bank b.
TypeOK =
    /\ dock \in Banks
    /\ occupants \in [Banks -> SUBSET (Missionaries \cup Cannibals)]

Init ==
    /\ dock = "east"
    /\ occupants = [b \in Banks |-> IF b = "east" THEN Missionaries \cup Cannibals ELSE {}]

\* Count missionaries on a bank.
MissionariesOn(b) == (occupants[b] \cap Missionaries).Cardinality
\* Always defined; a bank with no missionaries is trivially safe.
CannibalsOn(b) == (occupants[b] \cap Cannibals).Cardinality

\* A bank is safe if it has no missionaries, or cannibals do not outnumber them.
BankSafe(b) == (MissionariesOn(b) = 0) \/ (CannibalsOn(b) =< MissionariesOn(b))

\* The Move action carries a non-empty group across the river, but only if the
\* resulting distribution leaves both banks safe -- this is what forbids any
\* crossing that would let cannibals outnumber missionaries on departure or arrival.
Move ==
    /\ dock' \in Banks
    /\ dock' # dock
    /\ \E g \in SUBSET (Missionaries \cup Cannibals) :
        /\ Cardinality(g) >= MinLoad
        /\ Cardinality(g) <= BoatCap
        /\ g \subseteq occupants[dock]
        /\ occupants' = [occupants EXCEPT ![dock] = @ \ g, ![dock'] = @ \cup g]
    /\ BankSafe(dock)
    /\ BankSafe(dock')

Next == Move

\* SAFETY: no bank ever leaves a minority of missionaries in the hands of
\* cannibals, and the boat's occupancy stays within its rated capacity.
Solution ==
    /\ BankSafe("east")
    /\ BankSafe("west")
    /\ Cardinality(occupants["east"]) >= MinLoad
    /\ Cardinality(occupants["west"]) >= MinLoad
    /\ Cardinality(occupants["east"]) =< BoatCap
    /\ Cardinality(occupants["west"]) =< BoatCap

Spec == Init /\ [][Next]_vars

====