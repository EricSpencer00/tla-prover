---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Missionaries, \* Set of missionaires (e.g., {"M1","M2","M3"})
    Cannibals    \* Set of cannibals   (e.g., {"C1","C2","C3"})

VARIABLES 
    Boat,      \* The bank where the boat is currently docked: "East" or "West"
    WestBank   \* Subset of Missionaries ∪ Cannibals currently on the west bank

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
EastBank == Missionaries \cup Cannibals \ WestBank

People == Missionaries \cup Cannibals

\* True if the set of people on a bank respects the safety rule
Safe(bank) == 
    \A m \in Missionaries : 
        (m \in bank) => 
            Cardinality({c \in Cannibals : c \in bank}) <= Cardinality({mm \in Missionaries : mm \in bank})

\* The system is in a safe configuration on both banks
AllSafe == Safe(WestBank) /\ Safe(EastBank)

\* The number of people aboard the boat during a crossing
BoatCount == Cardinality({ p \in People : p \notin WestBank /\ p \notin EastBank }) 

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init == 
    /\ Boat = "East"
    /\ WestBank = {}
    /\ EastBank = People
    /\ AllSafe

\* ----------------------------------------------------------------------
\* The only possible move: a group of 1 or 2 people crosses the river
\* ----------------------------------------------------------------------
Move == 
    \E grp \subseteq (IF Boat = "East" THEN EastBank ELSE WestBank) :
        /\ Cardinality(grp) \in 1..2
        /\ LET newWest == 
                IF Boat = "East" 
                THEN WestBank \cup grp 
                ELSE WestBank \ grp
           IN 
               /\ WestBank' = newWest
               /\ Boat' = IF Boat = "East" THEN "West" ELSE "East"
               /\ AllSafe

\* ----------------------------------------------------------------------
\* Stuttering step to avoid deadlock when the goal is reached
\* ----------------------------------------------------------------------
Stutter == 
    /\ Boat' = Boat
    /\ WestBank' = WestBank
    /\ UNCHANGED << >>   \* No state change

Next == Move \/ Stutter

\* ----------------------------------------------------------------------
\* Safety invariant required by the cfg file
\* ----------------------------------------------------------------------
Solution == WestBank = People

\* ----------------------------------------------------------------------
\* Type-correctness invariant (optional but often useful)
\* ----------------------------------------------------------------------
TypeOK == 
    /\ Boat \in {"East", "West"}
    /\ WestBank \subseteq People
    /\ EastBank = People \ WestBank

=============================================================================