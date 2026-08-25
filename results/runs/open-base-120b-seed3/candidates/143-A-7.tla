---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Missionaries, Cannibals

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
Banks == {"East", "West"}

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

\* People on a bank are represented as a set of persons (missionaries or cannibals)
VARIABLES BoatLocation, People

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
IsMissionary(p) == p \in Missionaries
IsCannibal(p) == p \in Cannibals

Safe(bankPeople) ==
  /\ ( \A p \in bankPeople : ~IsMissionary(p) )               \* no missionaries
     \/ ( Cardinality({p \in bankPeople : IsCannibal(p)}) <=
          Cardinality({p \in bankPeople : IsMissionary(p)}) )

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ BoatLocation = "East"
  /\ People = [b \in Banks |-> IF b = "East"
                               THEN Missionaries \cup Cannibals
                               ELSE {}]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \E G \subseteq People[BoatLocation] :
    /\ Cardinality(G) \in 1..2                     \* boat carries 1 or 2
    /\ LET newEast ==
           IF BoatLocation = "East"
              THEN People["East"] \ G
              ELSE People["East"] \cup G
         newWest ==
           IF BoatLocation = "West"
              THEN People["West"] \ G
              ELSE People["West"] \cup G
       IN
         /\ Safe(newEast)
         /\ Safe(newWest)
         /\ BoatLocation' = Opposite(BoatLocation)
         /\ People' = [b \in Banks |-> IF b = "East" THEN newEast ELSE newWest]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<BoatLocation, People>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ BoatLocation \in Banks
  /\ People \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
  /\ \A b \in Banks :
        (People[b] \cap Missionaries) \cap Cannibals = {}   \* sets are disjoint
  /\ People["East"] \cup People["West"] = Missionaries \cup Cannibals

Solution == People["East"] # {}   \* violation (empty east bank) signals a solution

\* ----------------------------------------------------------------------
\* Theorem (optional, to help model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

=============================================================================