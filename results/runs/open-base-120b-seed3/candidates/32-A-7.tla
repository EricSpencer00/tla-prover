---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the faded color
    MeetingPlaceEmpty \* identifier for an empty meeting place

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Color == {Blue, Red, Yellow, Faded}
\* Blue, Red, Yellow are just symbols; they need not be declared as
\* separate constants.

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE IF (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) THEN
        Yellow
    ELSE IF (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN
        Red
    ELSE IF (c1 = Red /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red) THEN
        Blue
    ELSE
        Faded \* unreachable (both arguments are non‑faded)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    creatures,   \* [1..N -> [color: Color, count: Nat]]
    place,       \* MeetingPlaceEmpty or a creature id in 1..N
    meetingCount \* total number of completed meetings

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ place = MeetingPlaceEmpty
    /\ meetingCount = 0
    /\ \A c \in 1..N :
          \E col \in {Blue, Red, Yellow} :
              creatures[c] = [color |-> col, count |-> 0]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ place = MeetingPlaceEmpty
    /\ meetingCount < M
    /\ \E c \in 1..N :
          /\ creatures[c].color # Faded
          /\ place' = c
          /\ UNCHANGED <<creatures, meetingCount>>

FadeOut ==
    /\ place = MeetingPlaceEmpty
    /\ meetingCount = M
    /\ \E c \in 1..N :
          /\ creatures[c].color # Faded
          /\ creatures' = [creatures EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<place, meetingCount>>

Meet ==
    /\ place = p
    /\ p \in 1..N
    /\ meetingCount < M
    /\ \E c \in 1..N :
          /\ c # p
          /\ creatures[c].color # Faded
          /\ LET col1 == creatures[p].color
                 col2 == creatures[c].color
                 newCol == Complement(col1, col2)
             IN 
                /\ creatures' = [creatures EXCEPT 
                                   ![p] = [color |-> newCol,
                                           count |-> @.count + 1],
                                   ![c] = [color |-> newCol,
                                           count |-> @.count + 1]]
                /\ meetingCount' = meetingCount + 1
                /\ place' = MeetingPlaceEmpty

Next ==
    \/ Enter
    \/ FadeOut
    \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<creatures, place, meetingCount>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ creatures \in [1..N -> [color : Color, count : Nat]]
    /\ place \in MeetingPlaceEmpty \/ (1..N)
    /\ meetingCount \in Nat

\* ----------------------------------------------------------------------
\* Safety property: sum of individual counts when meetings are done
\* ----------------------------------------------------------------------
SumMet ==
    (meetingCount = M) => (\Sum c \in 1..N : creatures[c].count = 2 * M)

====