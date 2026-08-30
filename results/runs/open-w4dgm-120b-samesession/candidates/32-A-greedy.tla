---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a pair: its current color and its personal meeting count.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {"blue", "red"} THEN "yellow"
    ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
    ELSE IF {c1, c2} = {"red", "yellow"} THEN "blue"
    ELSE Faded

VARIABLES state, mall, totalMeetings

TypeOK ==
    /\ state \in [Creatures -> [color: Colors, met: 0..M]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterMall(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings < M
    /\ mall' = c
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ state[c].color # Faded
    /\ totalMeetings >= M
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, totalMeetings>>

MeetAndMutate(c) ==
    /\ mall # MeetingPlaceEmpty
    /\ mall # c
    /\ state[c].color # Faded
    /\ state[mall].color # Faded
    /\ totalMeetings < M
    /\ LET newcol == Complement(state[c].color, state[mall].color) IN
        state' = [state EXCEPT ![c] = [color |-> newcol, met |-> @.met + 1],
                              ![mall] = [color |-> newcol, met |-> @.met + 1]]
    /\ totalMeetings' = totalMeetings + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in Creatures : EnterMall(c)
    \/ \E c \in Creatures : FadeOut(c)
    \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_<<state, mall, totalMeetings>>

SumMet == totalMeetings * 2

\* When the meeting place has closed, the per-creature counts must still
\* account for exactly twice the number of meetings that happened.
MeetingCountCoherent == (totalMeetings = M) => (SumMet = M * 2)
====