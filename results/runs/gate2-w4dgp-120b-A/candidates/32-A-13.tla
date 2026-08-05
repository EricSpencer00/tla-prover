---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES colorAndCount, occupant, totalMeetings

vars == <<colorAndCount, occupant, totalMeetings>>

Colors == {"blue", "red", "yellow"}

\* The complement rule: given two colors, c1 and c2, return the resulting color
\* each creature adopts after a meeting.  Equality keeps the color; otherwise the
\* third color is chosen.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN CHOOSE c \in Colors : s \ {c} = {}

SumCounts ==
  LET f[S \in SUBSET 1..N] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN colorAndCount[x][2] + f[S \ {x}]
  IN f[1..N]

TypeOK ==
  /\ colorAndCount \in [1..N -> (Colors \cup {Faded}) \X (0..M)]
  /\ occupant \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ colorAndCount \in [1..N -> Colors \X {0}]
  /\ occupant = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* A creature enters the meeting place only while it is empty and the meeting
\* budget has not been spent; it waits there for a partner.
Enter(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ colorAndCount[c][1] # Faded
  /\ occupant' = c
  /\ UNCHANGED <<colorAndCount, totalMeetings>>

\* No more meetings can start once the budget is spent; a creature trying to
\* enter simply fades out instead of waiting indefinitely.
Fade(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ colorAndCount[c][1] # Faded
  /\ colorAndCount' = [colorAndCount EXCEPT ![c][1] = Faded]
  /\ UNCHANGED <<occupant, totalMeetings>>

\* Two distinct creatures meet: both adopt the complement color, both increase
\* their individual meeting count, and a meeting is recorded globally.
Meet(c) ==
  /\ occupant # MeetingPlaceEmpty
  /\ occupant # c
  /\ totalMeetings < M
  /\ LET newc1 == Complement(colorAndCount[occupant][1], colorAndCount[c][1]) IN
       /\ colorAndCount' = [colorAndCount EXCEPT ![occupant] = <<newc1, colorAndCount[occupant][2] + 1>>, ![c] = <<newc1, colorAndCount[c][2] + 1>>]
  /\ totalMeetings' = totalMeetings + 1
  /\ occupant' = MeetingPlaceEmpty

Next ==
  \/ \E c \in 1..N : Enter(c)
  \/ \E c \in 1..N : Fade(c)
  \/ \E c \in 1..N : Meet(c)

Spec == Init /\ [][Next]_vars

\* When the meeting budget is spent, every meeting that happened contributed
\* exactly two participants, so the sum of individual meeting counts is twice
\* the number of meetings recorded.
SumMet == totalMeetings = M => SumCounts = 2 * M

====