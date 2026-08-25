---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets

CONSTANTS Missionaries, Cannibals

(* ------------------------------------------------------------ *)
(* Derived sets *)
People == Missionaries \cup Cannibals
Bank   == {"East", "West"}

(* ------------------------------------------------------------ *)
(* State variables *)
VARIABLES Boat, East

(* West is defined as the complement of East *)
West == People \ East

(* ------------------------------------------------------------ *)
(* Helper definitions *)

Safe(bankSet) ==
  /\ (Missionaries \cap bankSet = {})           \* no missionaries, always safe
     \/ (Cardinality(Cannibals \cap bankSet) <= Cardinality(Missionaries \cap bankSet))

SafeAll ==
  /\ Safe(East)
  /\ Safe(West)

(* ------------------------------------------------------------ *)
(* Initialization *)

Init ==
  /\ Boat = "East"
  /\ East = People

(* ------------------------------------------------------------ *)
(* Next-state relation *)

Next ==
  \E g \subseteq People :
    /\ g # {}                                 \* at least one person
    /\ Cardinality(g) \in 1..2                \* boat capacity 1 or 2
    /\ (Boat = "East" => g \subseteq East)    \* board from current bank
    /\ (Boat = "West" => g \subseteq West)
    /\ LET newBoat == IF Boat = "East" THEN "West" ELSE "East"
           newEast == IF Boat = "East"
                        THEN East \ g
                        ELSE East \cup g
       IN
          /\ Boat' = newBoat
          /\ East' = newEast
          /\ SafeAll
    /\ UNCHANGED <<>>                         \* no other variables

(* ------------------------------------------------------------ *)
(* Type correctness invariant *)

TypeOK ==
  /\ Boat \in Bank
  /\ East \subseteq People

(* ------------------------------------------------------------ *)
(* Solution invariant (the east bank must stay non‑empty;
   violation indicates that everyone has reached the west bank) *)

Solution ==
  Cardinality(East) > 0

====