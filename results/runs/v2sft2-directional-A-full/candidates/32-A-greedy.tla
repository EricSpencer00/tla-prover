---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow", Faded}
Creatures == 1..N

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        IF c1 = "blue" THEN
            IF c2 = "red" THEN "yellow"
            ELSE "red"
        ELSE IF c1 = "red" THEN
            IF c2 = "blue" THEN "yellow"
            ELSE "blue"
        ELSE
            IF c2 = "blue" THEN "red"
            ELSE "blue"

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,          \* mapping from each creature to its current color
    counts,          \* mapping from each creature to its meeting count
    meetingPlace,    \* either MeetingPlaceEmpty or a creature identifier
    totalMeetings    \* global meeting counter

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [c \in Creatures |-> CHOOSE c \in {"blue", "red", "yellow"}]
    /\ counts = [c \in Creatures |-> 0]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ \E c \in Creatures :
          /\ colors[c] # Faded
          /\ meetingPlace' = c
          /\ UNCHANGED << colors, counts, totalMeetings >>

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ \E c \in Creatures :
          /\ colors[c] # Faded
          /\ colors' = [colors EXCEPT ![c] = Faded]
          /\ UNCHANGED << counts, meetingPlace, totalMeetings >>

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ \E c \in Creatures :
          /\ c # meetingPlace
          /\ colors[meetingPlace] # Faded
          /\ colors[c] # Faded
          /\ colors' = [colors EXCEPT ![meetingPlace] = Complement(colors[meetingPlace], colors[c]),
                                      ![c] = Complement(colors[meetingPlace], colors[c])]
          /\ counts' = [counts EXCEPT ![meetingPlace] = counts[meetingPlace] + 1,
                                      ![c] = counts[c] + 1]
          /\ totalMeetings' = totalMeetings + 1
          /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, counts, meetingPlace, totalMeetings>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ colors \in [Creatures -> Color]
    /\ counts \in [Creatures -> Nat]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual meeting counts equals twice the
\* global meeting counter when the global counter reaches the limit
\* ----------------------------------------------------------------------
SumMet ==
    totalMeetings = M => 
        \E s \in Nat :
            /\ s = \Sum c \in Creatures : counts[c]
            /\ s = 2 * totalMeetings

====