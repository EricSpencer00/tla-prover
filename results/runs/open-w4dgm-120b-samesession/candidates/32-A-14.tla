---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature state: a color (or Faded) together with the number of meetings it
\* has participated in. The meeting place holds at most one waiting creature.
VARIABLES creature, meetingPlace, totalMeetings

vars == <<creature, meetingPlace, totalMeetings>>

Creatures == 0..(N - 1)

\* The complement rule: same colors stay, different colors become the third.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE LET third(a, b) == CASE a = "blue" /\ b # "blue" -> "red"
                                 [] a = "red" /\ b # "red" -> "blue"
                                 [] OTHER -> "yellow"
         IN third(c1, c2)

Init ==
    /\ \E c \in [Creatures -> {"blue", "red", "yellow"}] :
         creature = [i \in Creatures |-> <<c[i], 0>>]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

EnterPlace(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ creature[i][1] # Faded
    /\ meetingPlace' = i
    /\ UNCHANGED <<creature, totalMeetings>>

\* When the meeting place has closed and a creature tries to enter, it fades.
Fade(i) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ creature[i][1] # Faded
    /\ creature' = [creature EXCEPT ![i] = <<Faded, creature[i][2]>>]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Both participants adopt the complemented color and advance their counters.
Meet(i) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # i
    /\ totalMeetings < M
    /\ creature[i][1] # Faded
    /\ creature[meetingPlace][1] # Faded
    /\ LET cnew == Complement(creature[i][1], creature[meetingPlace][1])
       IN creature' = [creature EXCEPT ![i] = <<cnew, creature[i][2] + 1>>,
                                     ![meetingPlace] = <<cnew, creature[meetingPlace][2] + 1>>]
    /\ totalMeetings' = totalMeetings + 1
    /\ meetingPlace' = MeetingPlaceEmpty

Next ==
    \/ \E i \in Creatures : EnterPlace(i)
    \/ \E i \in Creatures : Fade(i)
    \/ \E i \in Creatures : Meet(i)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M
    /\ \A i \in Creatures :
         /\ creature[i][1] \in {"blue", "red", "yellow", Faded}
         /\ creature[i][2] \in 0..M

\* Conservation: each meeting is counted once globally and once per participant,
\* so twice in total across all creatures, and nothing else ever changes it.
SumMet ==
    totalMeetings * 2 = creature[0][2] + creature[1][2] + creature[2][2]

====