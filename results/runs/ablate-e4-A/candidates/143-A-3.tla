---- MODULE MissionariesAndCannibals ----
EXTENDS FiniteSets

CONSTANTS Missionaries, Cannibals

Banks          == {"East", "West"}
PersonSet     == Missionaries \cup Cannibals

Opposite(b)   == IF b = "East" THEN "West" ELSE "East"

VARIABLES Boat, People

TypeOK == 
   /\ Boat \in Banks
   /\ People \in [Banks -> SUBSET PersonSet]
   /\ \A p \in PersonSet : p \in People["East"] \/ p \in People["West"]
   /\ People["East"] # People["West"]
   /\ People["East"] \/ People["West"] = PersonSet

SafeState(ppl) == 
   \A b \in Banks :
      IF Missionaries \cap ppl[b] = {} THEN TRUE
      ELSE (|Cannibals \cap ppl[b]| <= |Missionaries \cap ppl[b]|)

Init == 
   /\ Boat = "East"
   /\ People = [p \in Banks |-> IF p = "East" THEN PersonSet ELSE {}]
   /\ TypeOK

Next == 
   \E group \subseteq People[Boat] :
      /\ Len(group) >= 1 /\ Len(group) <= 2
      /\ /\ Boat' = Opposite(Boat)
          /\ People' = [p \in Banks |-> IF p = Opposite(Boat) THEN People[p] \cup group
                                            ELSE IF p = Boat THEN People[p] \ group
                                            ELSE People[p]]
          /\ SafeState(People')

Spec == Init /\ [][Next]_<<Boat, People>>

Solution == People["East"] # {}

====