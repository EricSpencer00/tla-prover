---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"East", "West"}
ALLPEOPLE == Missionaries \cup Cannibals

VARIABLES Boat, PeopleOnBank

\* Initial state: boat at East, all people on East, West empty
Init ==
    /\ Boat = "East"
    /\ PeopleOnBank = [b \in Banks |-> IF b = "East" THEN ALLPEOPLE ELSE {}]

\* Safety check for a bank: if missionaries are present, cannibals do not outnumber them
IsSafe(b) ==
    LET M == PeopleOnBank[b] \cap Missionaries
        C == PeopleOnBank[b] \cap Cannibals
    IN
        (M = {} ) \/ (#C <= #M)

\* Move action: one or two people cross the river
Move ==
    \E group \in Subset(ALLPEOPLE) :
        /\ (#group = 1 \/ #group = 2)
        /\ group \subseteq PeopleOnBank[Boat]
        /\ LET newBoat \in Banks : newBoat = IF Boat = "East" THEN "West" ELSE "East" IN
           /\ Boat' = newBoat
           /\ PeopleOnBank' = [PeopleOnBank EXCEPT
                                ![Boat] = (PeopleOnBank[Boat] \ group),
                                ![newBoat] = (PeopleOnBank[newBoat] \cup group)]
           /\ IsSafe("East")
           /\ IsSafe("West")

Next == Move

\* Type correctness and safety invariant
TypeOK ==
    /\ Boat \in Banks
    /\ PeopleOnBank \in [Banks -> SUBSET ALLPEOPLE]
    /\ \A p \in ALLPEOPLE :
           (p \in PeopleOnBank["East"]) xor (p \in PeopleOnBank["West"])
    /\ \A b \in Banks : IsSafe(b)

\* Invariant that the east bank is always non‑empty (used to find a solution when violated)
Solution == PeopleOnBank["East"] # {}

====