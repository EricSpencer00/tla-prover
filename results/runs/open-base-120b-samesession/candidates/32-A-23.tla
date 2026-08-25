---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* value representing a faded color
    MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Creatures == 1..N

Blue   == "Blue"
Red    == "Red"
Yellow == "Yellow"

Colors == {Blue, Red, Yellow, Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    state,   \* mapping from each creature to a record [color, count]
    place,   \* either MeetingPlaceEmpty or the id of a waiting creature
    total    \* total number of completed meetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Complement rule: given two colors, produce the new color after a meeting
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {Blue, Red}    THEN Yellow
    ELSE IF {c1, c2} = {Blue, Yellow} THEN Red
    ELSE IF {c1, c2} = {Red, Yellow}  THEN Blue
    ELSE Faded                     \* should never occur for valid inputs

\* Sum of all individual meeting counts
SumCounts == 
    \* Use the built‑in sum operator over a finite set
    Sum({ i \in Creatures : state[i].count })

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init ==
    /\ state \in [Creatures -> [color : Colors, count : Nat]]
    /\ \A i \in Creatures :
          /\ state[i].color \in {Blue, Red, Yellow}
          /\ state[i].count = 0
    /\ place = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in Creatures :
          /\ state[i].color # Faded
          /\ place' = i
          /\ UNCHANGED << state, total >>
          /\ UNCHANGED state   \* state unchanged
          /\ UNCHANGED total

FadeOut ==
    /\ place = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in Creatures :
          /\ state[i].color # Faded
          /\ state' = [state EXCEPT ![i].color = Faded]
          /\ UNCHANGED << place, total >>

MeetAndMutate ==
    /\ place \in Creatures
    /\ total < M
    /\ \E i \in Creatures :
          /\ i # place
          /\ state[i].color # Faded
          /\ state[place].color # Faded
          /\ LET
                c1 == state[i].color,
                c2 == state[place].color,
                newColor == Complement(c1, c2)
             IN
                /\ state' = [state EXCEPT 
                               ![i].color   = newColor,
                               ![i].count   = @ + 1,
                               ![place].color = newColor,
                               ![place].count = @ + 1]
                /\ total' = total + 1
                /\ place' = MeetingPlaceEmpty

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, place, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [Creatures -> [color : Colors, count : Nat]]
    /\ place \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    (total = M) => (SumCounts = 2 * M)

\* ----------------------------------------------------------------------
\* THEOREMS (for TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====