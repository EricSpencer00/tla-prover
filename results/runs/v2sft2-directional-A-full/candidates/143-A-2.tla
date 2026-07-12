---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, TLC

CONSTANTS Missionaries, Cannibals

Banks == {"East", "West"}

VARIABLES Boat, People

Opposite(b) == IF b = "East" THEN "West" ELSE "East"

Init ==
    /\ Boat = "East"
    /\ People = [b \in Banks |-> 
              IF b = "East" THEN Missionaries \cup Cannibals ELSE {}]

Move ==
    \E Group \subseteq People[Boat] :
          /\ 1 <= #Group
          /\ #Group <= 2
          /\ Boat' = Opposite(Boat)
          /\ People' = [b \in Banks |-> 
                  IF b = Boat THEN People[b] \ Group
                  ELSE IF b = Opposite(Boat) THEN People[b] \cup Group
                  ELSE People[b]]

Next == Move

Spec == Init /\ [][Next]_<<Boat, People>>

TypeOK ==
    /\ Boat \in Banks
    /\ People \in [Banks -> SUBSET (Missionaries \cup Cannibals)]
    /\ People["East"] \cup People["West"] = Missionaries \cup Cannibals
    /\ People["East"] \cap People["West"] = {}
    /\ \A b \in Banks :
           (|People[b] \cap Missionaries| > 0) =>
             (|People[b] \cap Cannibals| <= |People[b] \cap Missionaries|)

Solution ==
    People["East"] # {}

====