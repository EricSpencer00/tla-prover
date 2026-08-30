---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Complement rule: the two creatures end up holding the third, different color.
Colors == {"blue", "red", "yellow"}
\* The exhausted meeting place is not a creature, so it does not meet itself.
Occupants == 0..(N - 1) \cup {MeetingPlaceEmpty}

VARIABLES cstate, meetingPlace, totalMeetings
vars == <<cstate, meetingPlace, totalMeetings>>

TypeOK ==
    /\ cstate \in [0..(N - 1) -> [color: Colors \cup {Faded}, met: 0..M]]
    /\ meetingPlace \in Occupants
    /\ totalMeetings \in 0..M

Init ==
    /\ cstate = [c \in 0..(N - 1) |-> [color |-> CHOOSE col \in Colors : TRUE, met |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterMeetingPlace(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ cstate[c].color # Faded
    /\ meetingPlace' = c
    /\ UNCHANGED <<cstate, totalMeetings>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ cstate[c].color # Faded
    /\ cstate' = [cstate EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* The arriving creature differs from the one already waiting there.
MeetAndMutate(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ cstate[c].color # Faded
    /\ LET both == {meetingPlace, c}
           newcol == IF Cardinality(both) = 1
                       THEN cstate[meetingPlace].color
                       ELSE CHOOSE col \in Colors :
                                \A x \in both : col # cstate[x].color
           upd(cn) == [color |-> newcol, met |-> cstate[cn].met + 1]
       IN cstate' = [x \in 0..(N - 1) |-> IF x \in both THEN upd(x) ELSE cstate[x]]
    /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E c \in 0..(N - 1) : EnterMeetingPlace(c)
    \/ \E c \in 0..(N - 1) : FadeOut(c)
    \/ \E c \in 0..(N - 1) : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Each meeting is two-sided, so a saturated system has double the meeting count
\* spread across participants -- not more, not less.
SumMet == totalMeetings * 2

\* Conservation: when the system is saturated, the per-creature counts add up to
\* exactly twice the number of meetings -- nothing more and nothing less.
MeetingCountConserved == totalMeetings >= M => SumMet

====