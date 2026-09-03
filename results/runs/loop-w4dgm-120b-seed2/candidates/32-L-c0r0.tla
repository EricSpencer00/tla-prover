---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N. Each carries a color and a count of
\* meetings it has participated in. The meeting place holds at most one waiting
\* creature; a meeting is a two-way color complement between the occupant and an
\* arriving creature, and it advances both participants' counts and the global
\* meeting counter together.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, mall, totalMeetings

vars == <<state, mall, totalMeetings>>

TypeOK ==
  /\ state \in [Creatures -> [color: Colors, met: 0..M]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ state \in [Creatures -> [color: {"blue", "red", "yellow"}, met: 0]]
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* The complement rule: two identical colors stay unchanged; two different
\* colors both become the third, missing color.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN
       CHOOSE c \in {"blue", "red", "yellow"} : c \notin s

Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ state[c].color # Faded
  /\ mall' = c
  /\ UNCHANGED <<state, totalMeetings>>

FadeOut(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ state[c].color # Faded
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mall, totalMeetings>>

Meet(c) ==
  /\ mall # MeetingPlaceEmpty
  /\ mall # c
  /\ state[c].color # Faded
  /\ state[mall].color # Faded
  /\ totalMeetings < M
  /\ LET newc == Complement(state[c].color, state[mall].color) IN
       state' = [state EXCEPT ![c].color = newc, ![mall].color = newc,
                 ![c].met = @ + 1, ![mall].met = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ mall' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures: Enter(c)
  \/ \E c \in Creatures: FadeOut(c)
  \/ \E c \in Creatures: Meet(c)

Spec == Init /\ [][Next]_vars

\* Every meeting advances exactly two participants, so the sum of individual
\* meeting counts is twice the number of meetings that have occurred.
SumMet ==
  LET f[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN state[x].met + f[S \ {x}]
  IN f[Creatures]

\* When the meeting place has closed, the two-way accounting must still hold:
\* the global meeting counter is exactly half the summed per-creature counts.
MeetingCountCoherent == totalMeetings = SumMet \div 2

====