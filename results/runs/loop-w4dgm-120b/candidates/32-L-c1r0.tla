---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a pair: its current color and how many meetings it has attended.
\* The meeting place holds at most one waiting creature; the global meeting
\* counter reaches M, after which creatures that try to enter fade out.

Creatures == 0..(N - 1)
Colors == {"blue", "red", "yellow", Faded}
\* Color complement: two equal colors stay, two distinct colors turn the third.
Complement(x, y) == IF x = y THEN x
                     ELSE CASE x = "blue" /\ y = "red" => "yellow"
                               [] x = "red" /\ y = "blue" => "yellow"
                               [] x = "blue" /\ y = "yellow" => "red"
                               [] x = "yellow" /\ y = "blue" => "red"
                               [] OTHER => "blue"
                     END

VARIABLES state, waiting, totalMeetings
vars == <<state, waiting, totalMeetings>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
  /\ state \in [Creatures -> [color: Colors, attended: 0..M]]
  /\ waiting \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ state = [i \in Creatures |-> [color |-> CHOOSE c \in {"blue", "red", "yellow"} : TRUE, attended |-> 0]]
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings = 0

Enter(i) ==
  /\ waiting = MeetingPlaceEmpty
  /\ state[i].color # Faded
  /\ totalMeetings < M
  /\ waiting' = i
  /\ UNCHANGED <<state, totalMeetings>>

FadeOut(i) ==
  /\ waiting = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ state[i].color # Faded
  /\ state' = [state EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<waiting, totalMeetings>>

Meet(i) ==
  /\ waiting # MeetingPlaceEmpty
  /\ waiting # i
  /\ \/ state[i].color # Faded
        \/ state[waiting].color # Faded
  /\ LET mc == Complement(state[i].color, state[waiting].color) IN
       state' = [state EXCEPT ![i].color = mc, ![i].attended = @ + 1,
                              ![waiting].color = mc, ![waiting].attended = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ waiting' = MeetingPlaceEmpty

Next ==
  \/ \E i \in Creatures : Enter(i) \/ FadeOut(i) \/ Meet(i)

Spec == Init /\ [][Next]_vars

SumMet ==
  /\ totalMeetings = M => SumOver([i \in Creatures |-> state[i].attended], Creatures) = 2 * M

====