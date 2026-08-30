---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creators == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, meetingPlace, totalMeetings
vars == << state, meetingPlace, totalMeetings >>

NoMeeting == [col |-> "red", met |-> 0]

\* Complementation: both creatures take the third color not held by either,
\* or keep their color if they were already the same.
Complement(a, b) ==
  IF a = b THEN a
  ELSE IF {a, b} = {"blue", "red"} THEN "yellow"
  ELSE IF {a, b} = {"blue", "yellow"} THEN "red"
  ELSE "blue"

SumMet ==
  LET f[S \in SUBSET Creators] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN state[x].met + f[S \ {x}]
  IN f[Creators]

TypeOK ==
  /\ state \in [Creators -> [col : Colors, met : 0 .. M]]
  /\ meetingPlace \in Creators \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0 .. M

Init ==
  /\ state = [c \in Creators |-> NoMeeting]
  /\ \E c \in Creators : state[c].col \in {"blue", "red", "yellow"}
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ state[c].col # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED << state, totalMeetings >>

Fading(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ state[c].col # Faded
  /\ state' = [state EXCEPT ![c].col = Faded]
  /\ UNCHANGED << meetingPlace, totalMeetings >>

Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ totalMeetings < M
  /\ state[c].col # Faded
  /\ state[meetingPlace].col # Faded
  /\ LET newcol == Complement(state[c].col, state[meetingPlace].col)
     IN state' = [state EXCEPT ![c].col = newcol,
                           ![meetingPlace].col = newcol,
                           ![c].met = @ + 1,
                           ![meetingPlace].met = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creators : Enter(c) \/ Fading(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* When the meeting place has closed, the per-creature meeting counts add up to
\* exactly twice the number of meetings performed -- each meeting involved two.
NoLostUpdate == totalMeetings = M => SumMet = 2 * totalMeetings

====