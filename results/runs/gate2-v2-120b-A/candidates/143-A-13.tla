---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

(* --------------- Constants --------------- *)
CONSTANT Missionaries, Cannibals

(* --------------- Derived Sets --------------- *)
People == Missionaries \cup Cannibals

West  == 0
East  == 1
Banks == {West, East}
BoatPos == [bank : Banks]

(* --------------- Variables --------------- *)
VARIABLES bank, boatPos

(* --------------- Helper definitions --------------- *)
Count(set, subset) == Cardinality(set \cap subset)

MissionariesOn(b) == Count(bank[b], Missionaries)
CannibalsOn(b)   == Count(bank[b], Cannibals)

Safe(b) ==
    /\ (MissionariesOn(b) = 0) \/ (CannibalsOn(b) <= MissionariesOn(b))

TypeOK ==
    /\ bank \in [Banks -> SUBSET People]
    /\ boatPos \in Banks
    /\ Missionaries \subseteq People
    /\ Cannibals \subseteq People
    /\ Missionaries # {}
    /\ Cannibals # {}
    /\ Missionaries \cap Cannibals = {}
    /\ \A b \in Banks : Safe(b)

(* --------------- Initial state --------------- *)
Init ==
    /\ bank[East] = People
    /\ bank[West] = {}
    /\ boatPos = East
    /\ TypeOK

(* --------------- Actions --------------- *)

(* People that board the boat on the current bank *)
Boarders == { S \in SUBSET bank[boatPos] : Cardinality(S) \in 1..2 }

Move ==
    \E board \in Boarders :
        LET newBank == [b \in Banks |-> 
                          IF b = boatPos 
                          THEN bank[b] \ {board} 
                          ELSE bank[b] \cup board] IN
        /\ boatPos' = IF boatPos = East THEN West ELSE East
        /\ bank' = newBank
        /\ \A b \in Banks : Safe(b)
        /\ TypeOK

Next == Move

(* --------------- Invariant stating solution reached --------------- *)
Solution == bank[East] = {}

====