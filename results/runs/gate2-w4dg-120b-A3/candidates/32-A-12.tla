---- MODULE Chameneos ----
EXTENDS Naturals, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES colorCount, meetingPlace, totalMeetings

vars == <<colorCount, meetingPlace, totalMeetings>>

\* Every creature has a color (blue, red, yellow, or the absorbing faded
\* state) and a count of how many meetings it has participated in.  The
\* meeting place (the Mall) holds at most one waiting creature at a time.
\* The global counter records how many meetings have happened.
\* N is the number of creatures.  M is the total-meetings limit.

Creatures == 1..N

InitialColors == {"blue", "red", "yellow"}

\* Color complement rule: identical colors stay unchanged; two different
\* colors are replaced by the third hue, the one neither holds.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN CHOOSE c \in InitialColors : c \notin s

Sum(xs) == LET f[S \in SUBSET Creatures] ==
              IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE
                   IN xs[x] + f[S \ {x}]
           IN f[Creatures]

TypeOK ==
  /\ colorCount \in [Creatures -> [color: {"blue", "red", "yellow", Faded}, met: 0..M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ \E c \in [Creatures -> {"blue", "red", "yellow"}] :
       colorCount = [k \in Creatures |-> [color |-> c[k], met |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* A creature enters the empty meeting place only while the system has not yet
\* reached its meeting cap.
Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ colorCount[c].color # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<colorCount, totalMeetings>>

\* Once the cap is reached, a creature that tries to enter simply fades out.
FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ colorCount[c].color # Faded
  /\ colorCount' = [colorCount EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Two different creatures meet: both adopt the complement color, both
\* increment their personal count, and the global counter advances.
Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ totalMeetings < M
  /\ LET nc == Complement(colorCount[c].color, colorCount[meetingPlace].color)
       IN colorCount' = [colorCount EXCEPT ![c].color = nc, ![meetingPlace].color = nc,
                         ![c].met = @ + 1, ![meetingPlace].met = @ + 1]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Safety: once the global meeting count reaches the maximum, every creature
\* has exactly the number of meetings its own count records, so the sum of
\* individual counts is twice the number of meetings (each counted for two
\* participants).
SumMet ==
  totalMeetings = M => Sum([k \in Creatures |-> colorCount[k].met]) = 2 * totalMeetings

====