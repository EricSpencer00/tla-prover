---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a record holding its current color and how many meetings it
\* has taken part in.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Complement(x, y) ==
    IF x = y THEN x
    ELSE LET third(z) == IF z # x /\ z # y THEN z ELSE y IN
         CHOOSE z \in {"blue", "red", "yellow"} : z = third(z)

VARIABLES state, meetingPlace, totalMeetings

vars == <<state, meetingPlace, totalMeetings>>

SumOf(f, S) ==
    LET Add[T \in SUBSET S] ==
        IF T = {} THEN 0
        ELSE LET x == CHOOSE y \in T : TRUE IN f[x] + Add[T \ {x}]
    IN Add[S]

TypeOK ==
    /\ state \in [Creatures -> [color : Colors, participated : 0..M]]
    /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
    /\ totalMeetings \in 0..M

Init ==
    /\ \E c \in [Creatures -> Colors] :
        state = [k \in Creatures |-> [color |-> c[k], participated |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

Enter(k) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ state[k].color # Faded
    /\ totalMeetings < M
    /\ meetingPlace' = k
    /\ UNCHANGED <<state, totalMeetings>>

FadeOut(k) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ state[k].color # Faded
    /\ state' = [state EXCEPT ![k].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

Meet(k) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # k
    /\ state[k].color # Faded
    /\ totalMeetings < M
    /\ LET newCol == Complement(state[k].color, state[meetingPlace].color) IN
        state' = [state EXCEPT
                    ![k] = [color |-> newCol, participated |-> state[k].participated + 1],
                    ![meetingPlace] = [color |-> newCol, participated |-> state[meetingPlace].participated + 1]]
    /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E k \in Creatures : Enter(k)
    \/ \E k \in Creatures : FadeOut(k)
    \/ \E k \in Creatures : Meet(k)

Spec == Init /\ [][Next]_vars

\* At the moment the meeting place closes, every creature's own meeting
\* count still sums to exactly twice the total meeting counter -- each
\* meeting is accounted for at both of its participants.
SumMet ==
    (totalMeetings = M) => (SumOf([k \in Creatures |-> state[k].participated], Creatures) = 2 * M)

====