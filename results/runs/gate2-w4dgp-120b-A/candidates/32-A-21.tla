---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N: number of chameneos; M: max meetings; Faded: color marker after closure; MeetingPlaceEmpty: sentinel for an empty meeting place.

Creators == 1..N
Colors == {"blue", "red", "yellow"} \cup {Faded}

VARIABLES colorAndMet, meetingPlace, totalMet

vars == <<colorAndMet, meetingPlace, totalMet>>

TypeOK ==
  /\ colorAndMet \in [Creators -> [color: Colors, met: 0..M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0..M

\* Each meeting involves exactly two participants, so when the meeting budget is spent
\* the sum of individual meeting counts is exactly twice that budget.
SumMet ==
  totalMet = M => (LET f[S \in SUBSET Creators] ==
                     IF S = {} THEN 0
                     ELSE LET x == CHOOSE y \in S : TRUE IN colorAndMet[x].met + f[S \ {x}]
                   IN f[Creators])

Init ==
  /\ \E initColors \in [Creators -> Colors \ {"Faded"}] :
       colorAndMet = [c \in Creators |-> [color |-> initColors[c], met |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

EnterMeeting(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ colorAndMet[c].color # Faded
  /\ colorAndMet' = [colorAndMet EXCEPT ![c].met = @ + 1]
  /\ meetingPlace' = c
  /\ UNCHANGED totalMet

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ colorAndMet[c].color # Faded
  /\ totalMet = M
  /\ colorAndMet' = [colorAndMet EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMet>>

Complement(c1, c2) ==
  IF colorAndMet[c1].color = colorAndMet[c2].color THEN colorAndMet[c1].color
  ELSE LET x == colorAndMet[c1].color
           y == colorAndMet[c2].color
           z == {"blue", "red", "yellow"} \ {x, y}
       IN CHOOSE k \in z : TRUE

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ colorAndMet' = [colorAndMet EXCEPT ![c].color = Complement(c, meetingPlace),
                                      ![meetingPlace].color = Complement(c, meetingPlace),
                                      ![c].met = @ + 1, ![meetingPlace].met = @ + 1]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMet' = totalMet + 1

Next ==
  \/ \E c \in Creators : EnterMeeting(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

====