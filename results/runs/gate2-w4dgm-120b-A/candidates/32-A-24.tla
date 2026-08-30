---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0

Creatures == 1 .. N

Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, meetingPlace, totalMeetings

vars == <<state, meetingPlace, totalMeetings>>

TypeOK ==
  /\ state \in [Creatures -> [color : Colors, count : 0 .. M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0 .. M

Init ==
  /\ state \in [Creatures -> [color : {"blue", "red", "yellow"}, count : {0}]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* The complement rule behind the color change: if the two colors are the
\* same the pair keeps it; otherwise both adopt the third color.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET others == {"blue", "red", "yellow"} \ {c1, c2} IN CHOOSE c \in others : TRUE

\* A creature enters the empty meeting place only while the system has not
\* reached its meeting limit.
EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ state[c].color # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<state, totalMeetings>>

\* Once the meeting limit is reached, a creature that tries to enter fades
\* out instead of joining.
FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ state[c].color # Faded
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Two different creatures meet: both adopt the complement color and both
\* record participation. The meeting place is emptied for the next pair.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ totalMeetings < M
  /\ state[c].color # Faded
  /\ state[meetingPlace].color # Faded
  /\ LET newColor == Complement(state[c].color, state[meetingPlace].color) IN
       state' = [state EXCEPT ![c].color = newColor, ![meetingPlace].color = newColor,
                        ![c].count = @ + 1, ![meetingPlace].count = @ + 1]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \/ \E c \in Creatures : EnterMeetingPlace(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Each meeting is a two-way interaction, so when the system has closed off
\* after M meetings the summed participation must be exactly 2*M.
SumMet == (totalMeetings = M) =>
             (2 * M = LET f[S \in SUBSET Creatures] ==
                          IF S = {} THEN 0
                          ELSE LET x == CHOOSE y \in S : TRUE
                               IN state[x].count + f[S \ {x}]
                      IN f[Creatures])

StateConstraint == TypeOK

====