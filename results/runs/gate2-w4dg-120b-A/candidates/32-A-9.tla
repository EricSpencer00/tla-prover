---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature carries a color and a meeting count; the meeting place holds at
\* most one waiting creature; the global counter tracks completed meetings.
VARIABLES creatureAttr, meetingPlace, totalMeetings

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Complement(c, d) ==
  /\ c = d
  /\ c
Complement(c, d) ==
  /\ c # d
  /\ CHOOSE e \in Colors : e # c /\ e # d

\* Per-creature counts plus the global count stay coherent: total meetings is
\* exactly half the sum of all individual creature counts, so no meeting is
\* invented or lost.
TypeOK ==
  /\ creatureAttr \in [Creatures -> [color : Colors, count : 0..M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M
  /\ M >= 1
  /\ N >= 1

SumMet == totalMeetings = M => creatureAttr[1].count + creatureAttr[2].count + (IF N >= 3 THEN creatureAttr[3].count ELSE 0) = 2 * M

Init ==
  /\ \E c \in [Creatures -> Colors \ {Faded}]:
       creatureAttr = [x \in Creatures |-> [color |-> c[x], count |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* Empty place, capacity not reached: some non-faded creature enters to wait.
EnterPlace ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ \E c \in Creatures :
       /\ creatureAttr[c].color # Faded
       /\ meetingPlace' = c
  /\ UNCHANGED <<creatureAttr, totalMeetings>>

\* Capacity reached: a creature that cannot wait instead fades permanently.
FadeOut ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ \E c \in Creatures :
       /\ creatureAttr[c].color # Faded
       /\ creatureAttr' = [creatureAttr EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Two distinct creatures meet: both adopt the complement color and both
\* increment their individual counts, as does the global counter.
MeetAndMutate ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ \E c \in Creatures :
       /\ c # meetingPlace
       /\ creatureAttr[c].color # Faded
       /\ creatureAttr[meetingPlace].color # Faded
       /\ LET newc == Complement(creatureAttr[c].color, creatureAttr[meetingPlace].color) IN
            /\ creatureAttr' = [creatureAttr EXCEPT ![c].color = newc, ![c].count = @ + 1, ![meetingPlace].color = newc, ![meetingPlace].count = @ + 1]
       /\ meetingPlace' = MeetingPlaceEmpty
       /\ totalMeetings' = totalMeetings + 1

Next == EnterPlace \/ FadeOut \/ MeetAndMutate

Spec == Init /\ [][Next]_<<creatureAttr, meetingPlace, totalMeetings>>

====