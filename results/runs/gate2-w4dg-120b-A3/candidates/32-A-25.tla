---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature is identified by an integer in 1..N, and its record holds
\* both its current color and how many meetings it has taken part in.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES record, meetingPlace, meetingsTotal
vars == << record, meetingPlace, meetingsTotal >>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

TypeOK ==
  /\ record \in [Creatures -> [color: Colors, met: 0..(2 * M)]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ meetingsTotal \in 0..M

Init ==
  /\ record = [c \in Creatures |-> [color |-> CHOOSE w \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal = 0

Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal < M
  /\ record[c].color # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED << record, meetingsTotal >>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal >= M
  /\ record[c].color # Faded
  /\ record' = [record EXCEPT ![c].color = Faded]
  /\ UNCHANGED << meetingPlace, meetingsTotal >>

Complement(a, b) ==
  IF a = b THEN a
  ELSE CHOOSE c \in {"blue", "red", "yellow"} : c # a /\ c # b

\* A meeting only fires while the waiting creature is different from the
\* arriving one, and the occupant is reset to empty afterwards.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ record[c].color # Faded
  /\ meetingsTotal < M
  /\ record' = [record EXCEPT ![c].color = Complement(@, record[meetingPlace].color),
                              ![meetingPlace].color = Complement(record[meetingPlace].color, @),
                              ![c].met = @ + 1, ![meetingPlace].met = @ + 1]
  /\ meetingsTotal' = meetingsTotal + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures: Enter(c)
  \/ \E c \in Creatures: FadeOut(c)
  \/ \E c \in Creatures: MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  meetingsTotal = M => SumOver([c \in Creatures |-> record[c].met], Creatures) = 2 * M
====