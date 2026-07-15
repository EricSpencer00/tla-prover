---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Missionaries, \* set of missionary identifiers
    Cannibals    \* set of cannibal identifiers

(* ---------- Helper definitions ---------- *)

People == Missionaries \cup Cannibals

East  == "East"
West  == "West"
Banks == {East, West}

(* Boat location variable *)
VARIABLES
    boatPos,    \* which bank the boat is currently docked at
    eastBank,   \* set of people currently on the east bank
    westBank    \* set of people currently on the west bank

vars == <<boatPos, eastBank, westBank>>

(* ---------- Initial state ---------- *)

Init ==
    /\ boatPos = East
    /\ eastBank = People
    /\ westBank = {}

(* ---------- Type correctness invariant ---------- *)

TypeOK ==
    /\ boatPos \in Banks
    /\ eastBank \subseteq People
    /\ westBank \subseteq People
    /\ eastBank \cup westBank = People
    /\ eastBank \cap westBank = {}

(* ---------- Safety condition for a single bank ---------- *)

BankSafe(bankSet) ==
    (Missionaries \cap bankSet = {}) \/ 
    Cardinality(Cannibals \cap bankSet) <= Cardinality(Missionaries \cap bankSet)

Safe ==
    /\ BankSafe(eastBank)
    /\ BankSafe(westBank)

(* ---------- Boat capacity constraint ---------- *)

BoatCapacity(group) ==
    Cardinality(group) \in 1..2

(* ---------- Move action ---------- *)

Move ==
    \E group \in SUBSET(People) :
        /\ BoatCapacity(group)
        /\ IF boatPos = East
           THEN /\ group \subseteq eastBank
                /\ eastBank' = eastBank \ group
                /\ westBank' = westBank \cup group
                /\ boatPos' = West
           ELSE /\ group \subseteq westBank
                /\ westBank' = westBank \ group
                /\ eastBank' = eastBank \cup group
                /\ boatPos' = East
        /\ Safe            \* safety after the move
        /\ UNCHANGED <<>>

Next == Move

(* ---------- Liveness / solution condition ---------- *)

Solution == westBank = People

=============================================================================