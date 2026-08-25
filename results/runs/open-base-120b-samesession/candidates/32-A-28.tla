---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the faded color
    MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Blue   == "blue"
Red    == "red"
Yellow == "yellow"
Colors == {Blue, Red, Yellow, Faded}
LivingColors == {Blue, Red, Yellow}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    creatures,       \* [1..N -> [color : Colors, meetCount : Nat]]
    meetingPlace,    \* either MeetingPlaceEmpty or a creature id
    totalMeetings    \* Nat

vars == <<creatures, meetingPlace, totalMeetings>>

\* ----------------------------------------------------------------------
\* Helper function: complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {Blue, Red}    THEN Yellow
    ELSE IF {c1, c2} = {Red, Yellow} THEN Blue
    ELSE IF {c1, c2} = {Blue, Yellow} THEN Red
    ELSE Faded   \* should never happen

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ meetingPlace \in {MeetingPlaceEmpty} \/ (1..N)
    /\ totalMeetings \in Nat
    /\ totalMeetings <= M
    /\ creatures \in [1..N -> [color : Colors, meetCount : Nat]]
    /\ \A i \in 1..N: creatures[i].color \in Colors

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0
    /\ \A i \in 1..N:
        /\ creatures[i].color \in LivingColors
        /\ creatures[i].meetCount = 0

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature enters an empty meeting place
\* ----------------------------------------------------------------------
Enter ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in 1..N:
        /\ creatures[c].color # Faded
        /\ meetingPlace' = c
        /\ UNCHANGED <<creatures, totalMeetings>>

\* ----------------------------------------------------------------------
\* Action: after the limit is reached a creature that tries to enter fades
\* ----------------------------------------------------------------------
FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ \E c \in 1..N:
        /\ creatures[c].color # Faded
        /\ creatures' = [creatures EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* ----------------------------------------------------------------------
\* Action: two different creatures meet and mutate their colors
\* ----------------------------------------------------------------------
MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in 1..N:
        /\ c # meetingPlace
        /\ creatures[c].color # Faded
        /\ LET w == meetingPlace IN
           LET newCol == Complement(creatures[c].color, creatures[w].color) IN
           /\ creatures' = [creatures EXCEPT 
                  ![c].color = newCol,
                  ![c].meetCount = @ + 1,
                  ![w].color = newCol,
                  ![w].meetCount = @ + 1]
        /\ totalMeetings' = totalMeetings + 1
        /\ meetingPlace' = MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ Enter
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety property: sum of individual counts equals twice the number of meetings
\* ----------------------------------------------------------------------
SumMet ==
    totalMeetings = M => 
        Sum(i \in 1..N: creatures[i].meetCount) = 2 * M

====