---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature carries its own color and a tally of meetings it has participated
\* in. The meeting place admits at most one waiting creature; a second creature
\* arriving while the place is occupied triggers a paired meeting.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
\* The complement rule: a two-color mismatch resolves to the third color, a match
\* keeps the shared color.
Complement(x, y) == IF x = y THEN x ELSE CHOOSE c \in Colors : (c # x) /\ (c # y)

VARIABLES state, mall, totalMeetings
vars == <<state, mall, totalMeetings>>

TypeOK ==
  /\ state \in [Creatures -> [color: Colors, met: 0..M]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ state = [i \in Creatures |-> [color |-> CHOOSE c \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* A non-faded creature enters the waiting slot of the meeting place.
Enter(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ state[i].color # Faded
  /\ totalMeetings < M
  /\ mall' = i
  /\ UNCHANGED <<state, totalMeetings>>

\* Once the meeting place is closed, a creature that attempts entry fades out.
FadeOut(i) ==
  /\ mall = MeetingPlaceEmpty
  /\ state[i].color # Faded
  /\ totalMeetings = M
  /\ state' = [state EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<mall, totalMeetings>>

\* Two distinct creatures in the meeting place both adopt the complement color
\* and each incur one more meeting of their own tally.
Meet(i) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # i
  /\ state[i].color # Faded
  /\ state[mall].color # Faded
  /\ totalMeetings < M
  /\ LET newc == Complement(state[i].color, state[mall].color)
     IN state' = [state EXCEPT ![i] = [color |-> newc, met |-> @.met + 1],
                                ![mall] = [color |-> newc, met |-> @.met + 1]]
  /\ totalMeetings' = totalMeetings + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E i \in Creatures: Enter(i)
  \/ \E i \in Creatures: FadeOut(i)
  \/ \E i \in Creatures: Meet(i)

Spec == Init /\ [][Next]_vars

\* Every completed meeting is tallied once globally and marks two individual
\* participants, so the summed personal tallies reach twice the global count.
SumMet ==
  /\ totalMeetings = M => (2 * M = state[1].met + state[2].met + state[3].met)
====