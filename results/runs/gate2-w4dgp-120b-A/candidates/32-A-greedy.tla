---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N: number of chameneos (creatures); M: total meetings after which the meeting
\* place closes; Faded: the color a creature takes when it gives up; MeetingPlaceEmpty:
\* the empty value of the meeting place.

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

\* Complement: the third color not held by either creature, or the shared color if
\* they already match.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN CHOOSE c \in {"blue", "red", "yellow"} : c \notin s

VARIABLES color, met, meetingPlace, totalMet

vars == <<color, met, meetingPlace, totalMet>>

TypeOK ==
  /\ color \in [Creatures -> Colors]
  /\ met \in [Creatures -> 0..M]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0..M

Init ==
  /\ color \in [Creatures -> {"blue", "red", "yellow"}]
  /\ met = [c \in Creatures |-> 0]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

\* A non-faded creature enters the empty meeting place to wait for a partner.
Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet < M
  /\ color[c] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<color, met, totalMet>>

\* With the meeting place closed, a creature that tries to enter fades out.
Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = M
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED <<met, meetingPlace, totalMet>>

\* Two different creatures meet and both adopt the complement color.
Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ color[c] # Faded
  /\ color[meetingPlace] # Faded
  /\ totalMet < M
  /\ LET newc == Complement(color[c], color[meetingPlace]) IN
       color' = [color EXCEPT ![c] = newc, ![meetingPlace] = newc]
  /\ met' = [met EXCEPT ![c] = @ + 1, ![meetingPlace] = @ + 1]
  /\ totalMet' = totalMet + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* When the meeting place has closed, every meeting is accounted for exactly twice
\* (once per participant), so the sum of individual counts is twice the total.
SumMet ==
  totalMet = M => (LET f[S \in SUBSET Creatures] ==
                     IF S = {} THEN 0
                     ELSE LET x == CHOOSE y \in S : TRUE
                          IN met[x] + f[S \ {x}]
                   IN f[Creatures]) = 2 * M

====