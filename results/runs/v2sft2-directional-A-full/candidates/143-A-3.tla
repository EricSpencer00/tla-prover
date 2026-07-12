---- MODULE MissionariesAndCannibals ----
EXTENDS Naturals, Sequences

CONSTANTS Missionaries, Cannibals

\* Banks are represented as "East" and "West"
Banks == {"East", "West"}

\* The set of all people (both missionaries and cannibals)
People == Missionaries \cup Cannibals

\* Safe predicate for a bank: either no missionaries, or cannibals <= missionaries
Safe(bank) == 
  \E m \in Missionaries : 
     (m \in bank) => 
        \A c \in Cannibals : 
           (c \in bank) => 
              Len({c | c \in bank}) <= Len({m | m \in bank})

\* State variables
VARIABLES 
  boat,          \* the bank where the boat currently is
  onBank          \* a function mapping each bank to the set of people currently there

\* Initial state
Init == 
  /\ boat = "East"
  /\ onBank = [bank \in Banks |-> (IF bank = "East" THEN People ELSE {} )]

\* Helper: number of missionaries on a bank
MissionariesOn(bank) == { m \in Missionaries : m \in onBank[bank] }

\* Helper: number of cannibals on a bank
CannibalsOn(bank) == { c \in Cannibals : c \in onBank[bank] }

\* Helper: bank opposite to the current boat location
Opposite(bank) == IF bank = "East" THEN "West" ELSE "East"

\* The move action
Move ==
  \E p \in People :
    /\ p \in onBank[boat]                      \* person boards
    /\ \E q \in People \ {p} :
          /\ q \in onBank[boat]                \* second passenger (may be same as p if only one person)
          /\ Len({p, q}) <= 2                 \* at most two persons
          /\ \E newBank \in {Opposite(boat)} :
                /\ newBank = Opposite(boat)
                /\ \E destBank \in Banks :
                     /\ destBank = newBank
                     /\ \E srcBank \in Banks :
                          /\ srcBank = boat
                          /\ \E newOnBank \in [Banks -> SUBSET People] :
                               /\ newOnBank = [
                                    b \in Banks :
                                      IF b = srcBank THEN onBank[b] \ {p, q}
                                      ELSE IF b = destBank THEN onBank[b] \cup {p, q}
                                      ELSE onBank[b]
                               ]
                               /\ Safe(newOnBank[srcBank])
                               /\ Safe(newOnBank[destBank])
                               /\ \E b \in Banks : b \in Banks => newOnBank[b] \subseteq People
                               /\ /\ boat' = destBank
                                      /\ onBank' = newOnBank
                               ]

\* Next-state relation
Next == Move

\* Type correctness invariant
TypeOK == 
  /\ boat \in Banks
  /\ onBank \in [Banks -> SUBSET People]
  /\ \A b \in Banks : onBank[b] \subseteq People

\* Solution invariant: east bank becomes empty
Solution == onBank["East"] = {}

\* Specification
SPECIFICATION Spec == Init /\ [][Next]_<<boat, onBank>>

\* Safety invariant that the model checker will use
Safety == \A b \in Banks : (onBank[b] = {} \/ Len(CannibalsOn(b)) <= Len(MissionariesOn(b)))

====