---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* There are N creatures, each with an id in 1..N. Every creature carries a
\* (color, personalMeetings) pair. The meeting place admits a single waiting
\* creature at a time; two different creatures meeting there both adopt a new
\* color from the complement rule. The global counter records how many meetings
\* have happened in total.

Creatures == 1..N
Colors == {"blue", "red", "yellow"}
AliveColors == Colors \cup {Faded}

VARIABLES cstate, meetingPlace, totalMeetings

vars == <<cstate, meetingPlace, totalMeetings>>

TypeOK ==
  /\ cstate \in [Creatures -> [color : AliveColors, meetings : 0..2*M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ cstate = [i \in Creatures |-> [color |-> CHOOSE k \in Colors : TRUE, meetings |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

AllFaded == \A i \in Creatures : cstate[i].color = Faded

\* The meeting place lets one creature wait; entry is refused once the global
\* meeting budget has been spent, which is how creatures become faded.
Enter ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E i \in Creatures :
       /\ cstate[i].color # Faded
       /\ meetingPlace' = i
  /\ UNCHANGED <<cstate, totalMeetings>>

FadeOut ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ \E i \in Creatures :
       /\ cstate[i].color # Faded
       /\ cstate' = [cstate EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Complement rule: two equal colors stay that color; two different colors
\* both become the third, missing color.
Complement(a, b) ==
  IF a = b THEN a
  ELSE LET missing == CHOOSE c \in Colors : c # a /\ c != b IN missing

Meet ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ \E i \in Creatures :
       /\ i # meetingPlace
       /\ cstate[i].color # Faded
       /\ cstate[meetingPlace].color # Faded
       /\ LET newcol == Complement(cstate[i].color, cstate[meetingPlace].color) IN
            /\ cstate' = [cstate EXCEPT ![i] = [color |-> newcol, meetings |-> @.meetings + 1],
                                  ![meetingPlace] = [color |-> newcol, meetings |-> @.meetings + 1]]
       /\ totalMeetings' = totalMeetings + 1
       /\ meetingPlace' = MeetingPlaceEmpty
  /\ UNCHANGED <<\* meetingPlace already updated; nothing else changes\* >>

Next == Enter \/ FadeOut \/ Meet

Spec == Init /\ [][Next]_vars

\* Each meeting is a two-person event, so once the meeting budget is spent the
\* sum of individual meeting counts must be exactly twice the number of meetings.
SumMet ==
  /\ totalMeetings = M
  /\ (2 * M) = (cstate[1].meetings + cstate[2].meetings + cstate[3].meetings)

====