---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is identified by a number from 1 to N.
Agents == 1..N
Colors == {Faded, "blue", "red", "yellow"}

\* Complement rule: if two creatures differ they both adopt the third color.
ComplementOf(a, b) ==
  IF a = b THEN a
  ELSE LET s == {a, b} IN CHOOSE c \in Colors \ s : TRUE

VARIABLES attrib, meetingPlace, totalMet

vars == <<attrib, meetingPlace, totalMet>>

TypeOK ==
  /\ attrib \in [Agents -> [clr : Colors, count : 0..M]]
  /\ meetingPlace \in Agents \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0..M

Init ==
  /\ attrib = [a \in Agents |-> [clr |-> "blue", count |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

\* A creature that is not yet faded enters the empty meeting place.
Enter(a) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet < M
  /\ attrib[a].clr # Faded
  /\ meetingPlace' = a
  /\ UNCHANGED <<attrib, totalMet>>

\* When the meeting place is closed, a creature that tries to enter fades out.
FadeOut(a) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = M
  /\ attrib[a].clr # Faded
  /\ attrib' = [attrib EXCEPT ![a].clr = Faded]
  /\ UNCHANGED <<meetingPlace, totalMet>>

\* Two different creatures meet, both change color, and both record the meeting.
MeetAndMutate(a) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ a # meetingPlace
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMet' = totalMet + 1
  /\ attrib' = [attrib EXCEPT ![a] = [clr |-> ComplementOf(attrib[a].clr, attrib[meetingPlace].clr), count |-> attrib[a].count + 1],
                               ![meetingPlace] = [clr |-> ComplementOf(attrib[a].clr, attrib[meetingPlace].clr), count |-> attrib[meetingPlace].count + 1]]

Next == \E a \in Agents : Enter(a) \/ FadeOut(a) \/ MeetAndMutate(a)

\* Each meeting involves exactly two participants, so the system-wide total of
\* individual meeting counts is twice the number of meetings that have occurred.
ParticipationSum ==
  LET sum(F, S) ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN F[x] + sum(F, S \ {x})
  IN sum([a \in Agents |-> attrib[a].count], Agents)

Spec == Init /\ [][Next]_vars

SumMet == totalMet = M => ParticipationSum = 2 * M

====