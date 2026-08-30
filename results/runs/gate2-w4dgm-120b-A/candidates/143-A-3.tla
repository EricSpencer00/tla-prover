---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

Banks == {"east", "west"}
People == Missionaries \cup Cannibals
MaxCap == 2
NoMove == 0

VARIABLES location, boatAt, onboard

vars == <<location, boatAt, onboard>>

\* A bank is safe if it has no missionaries, or the cannibals do not outnumber them.
SafetyOn(b) ==
    LET mc == Cardinality(Missionaries \cap location[b])
        cc == Cardinality(Cannibals \cap location[b])
    IN mc = 0 \/ cc <= mc

TypeOK ==
    /\ location \in [Banks -> SUBSET People]
    /\ boatAt \in Banks
    /\ onboard \in 0..NoMove \cup 1..MaxCap

Init ==
    /\ location = [b \in Banks |-> IF b = "east" THEN People ELSE {}]
    /\ boatAt = "east"
    /\ onboard = NoMove

\* The move is atomic: the people board, the boat crosses, and they disembark.
Move ==
    /\ onboard = NoMove
    /\ \E s \in SUBSET location[boatAt] :
        /\ Cardinality(s) \in 1..MaxCap
        /\ LET other == IF boatAt = "east" THEN "west" ELSE "east" IN
            /\ Cardinality(location[other] \cup s) <= MaxCap
            /\ Cardinality(Missionaries \cap (location[other] \cup s))
                 >= Cardinality(Cannibals \cap (location[other] \cup s))
            /\ Cardinality(Missionaries \cap (location[boatAt] \ s))
                 >= Cardinality(Cannibals \cap (location[boatAt] \ s))
            /\ location' = [location EXCEPT ![boatAt] = @ \ s, ![other] = @ \cup s]
            /\ boatAt' = other
            /\ onboard' = Cardinality(s)

Next == Move

\* Missionaries never outnumbered by cannibals on either bank, and every crossing
\* carries at least one person and at most the boat's capacity.
TypeOK == TypeOK
Solution == \A b \in Banks : SafetyOn(b)

====