---- MODULE MissionariesAndCannibals ----
EXTENDS Integers, FiniteSets

CONSTANTS Missionaries, Cannibals

People == Missionaries \cup Cannibals

VARIABLES boatAt, banks, move

vars == <<boatAt, banks, move>>

Banks == {"east", "west"}
Crowd == [east : SUBSET People, west : SUBSET People]

TypeOK ==
    /\ boatAt \in Banks
    /\ banks \in Crowd
    /\ move \in {"idle", "m1", "m2"}

Init ==
    /\ boatAt = "east"
    /\ banks = [east |-> People, west |-> {}]
    /\ move = "idle"

Load(n) == IF n = 1 THEN "m1" ELSE "m2"

\* The boat crosses the river carrying one or two people. It may only fire when
\* the resulting populations on both banks would still be safe.
Move ==
    /\ move = "idle"
    /\ \E g \in (SUBSET banks[boatAt]) \ {{}} :
        /\ Cardinality(g) <= 2
        /\ Cardinality(banks[boatAt]) - Cardinality(g) >= Cardinality(g)
        /\ banks' = [banks EXCEPT ![boatAt] = @ \ g, ![IF boatAt = "east" THEN "west" ELSE "east"] = @ \cup g]
    /\ boatAt' = IF boatAt = "east" THEN "west" ELSE "east"
    /\ move' = Load(Cardinality(g))

Next == Move

\* Missionaries are safe on a bank only when they are not outnumbered by
\* cannibals; a bank with no missionaries is trivially safe.
MissionarySafety ==
    \A b \in Banks :
        \/ Missionaries \cap banks[b] = {}
        \/ Cardinality(Cannibals \cap banks[b]) <= Cardinality(Missionaries \cap banks[b])

\* Every actual move carries at least one person and at most the river's rated
\* capacity of two.
MoveWithinCapacity == move \in {"idle", "m1", "m2"}

TypeOKState == TypeOK /\ MissionarySafety /\ MoveWithinCapacity

\* The puzzle is solved once the east bank has been emptied by a safe sequence
\* of moves. Model-checking a violation of this is how a solution trace is
\* drawn out of the state space.
Solution == banks["east"] = {}

Spec == Init /\ [][Next]_vars

====