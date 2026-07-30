---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Colors: the three active chameneos colors, plus the faded state.
Colors == {"blue", "red", "yellow", Faded}

\* Complementation: if the two meeting colors are the same each keeps it;
\* if they are different both adopt the third (complement) color.
Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE LET candidates == Colors \ {"blue", "red", "yellow", Faded}
       IN CHOOSE c \in candidates :
            (c # c1 /\ c # c2)

VARIABLES cham, meetingPlace, totalMeetings
vars == <<cham, meetingPlace, totalMeetings>>

\* Each creature is recorded as a pair: its color and its meeting count.
Chams == [N -> [color : Colors, met : 0..M]]

RECURSIVE SumMet(_)
SumMet(S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE IN cham[x].met + SumMet(S \ {x})

TypeOK ==
  /\ cham \in Chams
  /\ meetingPlace \in N \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ \E c \in [N -> Colors \ {"faded"}] :
        cham' = [x \in N |-> [color |-> c[x], met |-> 0]]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = 0

\* A non-faded creature enters the empty meeting place before the limit.
Enter(x) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ cham[x].color # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = x
  /\ UNCHANGED <<cham, totalMeetings>>

\* Fade out: the place has closed and a creature cannot wait.
FadeOut(x) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ cham[x].color # Faded
  /\ totalMeetings = M
  /\ cham' = [cham EXCEPT ![x].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Two distinct creatures meet and both adopt the complement of their colors.
MeetAndMutate(x) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # x
  /\ cham[x].color # Faded
  /\ cham[meetingPlace].color # Faded
  /\ totalMeetings < M
  /\ LET newc == Complement(cham[x].color, cham[meetingPlace].color) IN
       /\ cham' = [cham EXCEPT ![x].color = newc,
                             ![meetingPlace].color = newc,
                             ![x].met = @ + 1,
                             ![meetingPlace].met = @ + 1]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \E x \in N : Enter(x) \/ FadeOut(x) \/ MeetAndMutate(x)

Spec == Init /\ [][Next]_vars

\* Conservation: when the meeting limit is reached, each creature's met
\* count sums to exactly twice the number of meetings performed.
SumMet == totalMeetings = M => SumMet(N) = 2 * M

====