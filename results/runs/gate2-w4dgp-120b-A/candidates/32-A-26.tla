---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}

\* Whole-system meeting counter; each creature tracks its own meetings.
VARIABLES colorCount, waitingAtPlace, totalMeetings

vars == <<colorCount, waitingAtPlace, totalMeetings>>

\* Pairwise complement: same leaves them unchanged; different gives the third.
Complement(a, b) ==
  IF a = b THEN a
  ELSE LET s == {a, b} IN CHOOSE c \in Colors : c \notin s

\* A creature may enter the meeting place and wait only when it is not faded.
NotFaded(c) == colorCount[c].color # Faded

SumOfCounts ==
  LET add[i \in 0..N] == IF i = 0 THEN 0 ELSE add[i - 1] + colorCount[i - 1].count IN add[N]

TypeOK ==
  /\ colorCount \in [Creatures -> [color : Colors, count : 0..M]]
  /\ waitingAtPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ \E f \in [Creatures -> Colors] :
       \A c \in Creatures : colorCount[c] = [color |-> f[c], count |-> 0]
  /\ waitingAtPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterPlace(c) ==
  /\ waitingAtPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ NotFaded(c)
  /\ waitingAtPlace' = c
  /\ UNCHANGED <<colorCount, totalMeetings>>

FadeOut(c) ==
  /\ waitingAtPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ NotFaded(c)
  /\ colorCount' = [colorCount EXCEPT ![c] = [color |-> Faded, count |-> @.count]]
  /\ UNCHANGED <<waitingAtPlace, totalMeetings>>

\* Two distinct creatures meet; both adopt the same new color.
Meet(c) ==
  /\ waitingAtPlace # MeetingPlaceEmpty
  /\ waitingAtPlace # c
  /\ NotFaded(c)
  /\ NotFaded(waitingAtPlace)
  /\ LET newcol == Complement(colorCount[c].color, colorCount[waitingAtPlace].color) IN
       /\ colorCount' = [colorCount EXCEPT ![c] = [color |-> newcol, count |-> @.count + 1],
                                          ![waitingAtPlace] = [color |-> newcol, count |-> @.count + 1]]
  /\ totalMeetings' = totalMeetings + 1
  /\ waitingAtPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterPlace(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* At the meeting limit every creature's meetings sum to exactly twice the
\* number of meetings, because each meeting involves two participants.
SumMet == (totalMeetings = M) => (SumOfCounts = 2 * M)

====