---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N; a creature can be in the meeting
\* place (the mall) or waiting, but never both.
CREATURES == 1..N
COLORS == {"blue", "red", "yellow", Faded}

VARIABLES state, mall, totalMeetings

vars == <<state, mall, totalMeetings>>

SumOf(f) == LET add[S \in SUBSET CREATURES] ==
                  IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE
                       IN f[x] + add[S \ {x}]
            IN add[CREATURES]

TypeOK ==
    /\ state \in [CREATURES -> [color: COLORS, met: 0..M]]
    /\ mall \in CREATURES \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ \E initColors \in [CREATURES -> {"blue", "red", "yellow"}] :
        state = [c \in CREATURES |-> [color |-> initColors[c], met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* Enter: a non-faded creature takes the empty meeting place.
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings < M
    /\ mall' = c
    /\ UNCHANGED <<state, totalMeetings>>

\* When the place is closed (meeting budget spent), a creature that tries to
\* enter instead fades out there and then.
FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings >= M
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMeetings>>

\* MeetAndMutate: the arriving creature meets the waiting one in the mall,
\* both adopt the complementary color, and both get credit for the meeting.
MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ c # mall
    /\ totalMeetings < M
    /\ totalMeetings' = totalMeetings + 1
    /\ state' = [x \in CREATURES |->
                    IF x \in {c, mall}
                        THEN [color |-> LET ca == state[c].color
                                            cb == state[mall].color
                                            Complement(a, b) ==
                                                IF a = b THEN a
                                                ELSE (IF a = "red" /\ b = "blue"
                                                      \/ a = "blue" /\ b = "red"
                                                      THEN "yellow"
                                                      ELSE IF a = "red" /\ b = "yellow"
                                                            \/ a = "yellow" /\ b = "red"
                                                            THEN "blue"
                                                            ELSE "red")
                                            IN Complement(ca, cb), met |-> state[x].met + 1]
                        ELSE state[x]]
    /\ mall' = MeetingPlaceEmpty

Next == \E c \in CREATURES : Enter(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Every meeting credits two participants, so once the budget is spent the
\* sum of individual meeting counts is exactly twice the total meetings.
SumMet == totalMeetings = M => SumOf([c \in CREATURES |-> state[c].met]) = 2 * M

====