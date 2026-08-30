---- MODULE Chameneos ----
EXTENDS Integers, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

\* Entry: the creature's current color; Count: how many meetings it has done.
VARIABLES state, meetingPlace, totalMeetings

vars == <<state, meetingPlace, totalMeetings>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
  /\ state \in [Creatures -> [Entry : Colors, Count : 0 .. M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0 .. M

Init ==
  /\ state \in [Creatures -> [Entry : Colors \ {Faded}, Count : 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* A creature that cannot enter because the limit has been reached fades.
EnterWaiting(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ state[c].Entry # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = c
  /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ state[c].Entry # Faded
  /\ totalMeetings >= M
  /\ state' = [state EXCEPT ![c].Entry = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

Complement(a, b) ==
  IF a = b THEN a
  ELSE LET S == {"blue", "red", "yellow"} IN S \ {a, b}

\* Two distinct participants meet; both adopt the complement color.
Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ totalMeetings < M
  /\ state[c].Entry # Faded
  /\ LET newColor == Complement(state[c].Entry, state[meetingPlace].Entry) IN
       /\ state' = [state EXCEPT ![c] = [Entry |-> newColor, Count |-> @.Count + 1],
                           ![meetingPlace] = [Entry |-> newColor, Count |-> @.Count + 1]]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \/ \E c \in Creatures : EnterWaiting(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Every meeting gives exactly two participants, so at the limit the
\* per-creature counts sum to exactly twice the number of meetings.
SumMet == totalMeetings = M => SumOver([c \in Creatures |-> state[c].Count], Creatures) = 2 * M
====