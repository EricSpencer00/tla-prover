---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* value representing the faded color
    MeetingPlaceEmpty   \* value representing an empty meeting place

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Blue   == "blue"
Red    == "red"
Yellow == "yellow"

Color == {Blue, Red, Yellow, Faded}
NonFadedColors == {Blue, Red, Yellow}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    creatures,   \* mapping i \in 1..N -> [color : Color, count : Nat]
    place,       \* either a creature id in 1..N or MeetingPlaceEmpty
    total        \* total number of completed meetings

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    CASE c1 = c2 -> c1
    [] (c1 = Blue  /\ c2 = Red)   \/ (c1 = Red   /\ c2 = Blue)   -> Yellow
    [] (c1 = Blue  /\ c2 = Yellow)\/ (c1 = Yellow/\ c2 = Blue)   -> Red
    [] (c1 = Red   /\ c2 = Yellow)\/ (c1 = Yellow/\ c2 = Red)   -> Blue

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ creatures \in [1..N -> [color : Color, count : Nat]]
    /\ \A i \in 1..N :
          /\ creatures[i].color \in NonFadedColors
          /\ creatures[i].count = 0
    /\ place = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ place = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ creatures[i].color # Faded
          /\ place' = i
          /\ UNCHANGED <<creatures, total>>

Fade ==
    /\ place = MeetingPlaceEmpty
    /\ total >= M
    /\ \E i \in 1..N :
          /\ creatures[i].color # Faded
          /\ creatures' = [creatures EXCEPT ![i].color = Faded]
          /\ UNCHANGED <<place, total>>

Meet ==
    /\ place # MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in 1..N :
          /\ i # place
          /\ creatures[i].color # Faded
          /\ creatures[place].color # Faded
          /\ LET c1  == creatures[i].color
                 c2  == creatures[place].color
                 newc == Complement(c1, c2)
             IN
                /\ creatures' = [creatures EXCEPT
                                   ![i].color = newc,
                                   ![i].count = @ + 1,
                                   ![place].color = newc,
                                   ![place].count = @ + 1]
          /\ total' = total + 1
          /\ place' = MeetingPlaceEmpty
          /\ UNCHANGED <<>>

Next == \/ Enter \/ Fade \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<creatures, place, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ creatures \in [1..N -> [color : Color, count : Nat]]
    /\ place \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    /\ total = M
    => LET sum == Sum({creatures[i].count : i \in 1..N})
       IN sum = 2 * M

\* ----------------------------------------------------------------------
\* The set of invariants to be checked by TLC (as required by the .cfg file)
\* ----------------------------------------------------------------------
\* INVARIANTS: TypeOK, SumMet
====