---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are indexed 1..N. Their colors come from three performing shades
\* plus a terminal "faded" shade used once the meeting place closes.
Colors == {"blue", "red", "yellow", Faded}
ActiveColors == {"blue", "red", "yellow"}

VARIABLES state, meetingPlace, totalMeetings
vars == <<state, meetingPlace, totalMeetings>>

\* The complement rule: both creatures adopt the third color when they differ.
Complement(c1, c2) ==
  LET a == {c1, c2} IN
    IF a = ActiveColors THEN CHOOSE c \in ActiveColors : c \notin a ELSE c1

TypeOK ==
  /\ state \in [1..N -> (Colors \X (0..M))]
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ state = [c \in 1..N |-> CHOOSE col \in ActiveColors : TRUE, 0]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterEmpty(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ state[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ state[c][1] # Faded
  /\ state' = [state EXCEPT ![c] = <<Faded, state[c][2]>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* A real meeting: both creatures change color and advance their own counts.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ LET w == meetingPlace IN
     /\ state' = [state EXCEPT ![c] = <<Complement(state[c][1], state[w][1]), @ + 1],
                              ![w] = <<Complement(state[c][1], state[w][1]), @ + 1>>]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in 1..N : EnterEmpty(c)
  \/ \E c \in 1..N : FadeOut(c)
  \/ \E c \in 1..N : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* At the limit, every recorded meeting accounts for exactly two participants.
SumMet ==
  (totalMeetings = M) =>
    (LET f[n \in 0..N] ==
        IF n = 0 THEN 0
        ELSE f[n - 1] + state[n][2]
     IN f[N] = 2 * M)
====