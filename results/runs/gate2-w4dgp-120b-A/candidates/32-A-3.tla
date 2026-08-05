---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES state, meetingPlace, meetings
vars == <<state, meetingPlace, meetings>>

NONE == "none"

Colors == {"blue", "red", "yellow", Faded}

\* Complementation: same colors stay unchanged; different colors both become the
\* third one not held by either creature.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE CHOOSE c3 \in {"blue", "red", "yellow"} : c3 # c1 /\ c3 # c2

InitState == [i \in 1..N |-> [color |-> "blue", count |-> 0]]

Init ==
  /\ state = InitState
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetings = 0

\* A creature enters the empty meeting place to wait for a partner.
Enter(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetings < M
  /\ state[i].color # Faded
  /\ meetingPlace' = i
  /\ UNCHANGED <<state, meetings>>

\* Once the meeting place is closed, a creature that tries to enter fades out
\* instead of waiting, keeping its meeting count.
FadeOut(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetings >= M
  /\ state[i].color # Faded
  /\ state' = [state EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<meetingPlace, meetings>>

\* Two different creatures meet and both change color according to the rule.
Meet(j) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # j
  /\ state[j].color # Faded
  /\ state[meetingPlace].color # Faded
  /\ state' = [state EXCEPT ![meetingPlace].color = Complement(state[meetingPlace].color, state[j].color), ![j].color = Complement(state[meetingPlace].color, state[j].color), ![meetingPlace].count = state[meetingPlace].count + 1, ![j].count = state[j].count + 1]
  /\ meetings' = meetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : FadeOut(i)
  \/ \E j \in 1..N : Meet(j)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ state \in [1..N -> [color : Colors, count : 0..M]]
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ meetings \in 0..M

\* Every completed meeting is accounted for exactly once per participant.
SumMet ==
  meetings = M => (\E i \in 1..N : state[i].count = M) \/ (meetings = 0 /\ \A i \in 1..N : state[i].count = 0) \/ (\A i \in 1..N : state[i].color = Faded)
====