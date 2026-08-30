---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a (color, personal meeting count) pair; colors are the three
\* base colors plus the special faded color a creature takes at shutdown.
Creatures == {1, 2, 3}
Colors == {"blue", "red", "yellow", Faded}
BaseColors == {"blue", "red", "yellow"}
ColorExcl(x, y) ==
  IF x = y THEN x
  ELSE IF {x, y} = {"blue", "red"} THEN "yellow"
  ELSE IF {x, y} = {"blue", "yellow"} THEN "red"
  ELSE "blue"

VARIABLES state, mall, totalMeetings

vars == <<state, mall, totalMeetings>>

TypeOK ==
  /\ state \in [Creatures -> [color : Colors, personal : 0..M]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

\* Every creature that has participated in a meeting is counted once per
\* meeting it took part in, so the sum must be exactly twice the number of
\* meetings: each meeting is a two-way handshake.
SumMet ==
  /\ totalMeetings = M
  /\ (2 * M) = Cardinality(Creatures) * M
       - Cardinality({c \in Creatures : state[c].color = Faded})
       - Cardinality({c \in Creatures : state[c].personal = 0})

Init ==
  /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in BaseColors : TRUE, personal |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterMall(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ state[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ state[c].color # Faded
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, totalMeetings>>

MeetAndMutate(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ state[c].color # Faded
  /\ state[mall].color # Faded
  /\ LET newcol == ColorExcl(state[c].color, state[mall].color) IN
       state' = [state EXCEPT ![c].color = newcol, ![c].personal = @ + 1,
                                 ![mall].color = newcol, ![mall].personal = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterMall(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

====