---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by the numbers 1..N; each carries a color and the
\* number of meetings it has participated in. The meeting place holds at most
\* one waiting creature at a time.
Creatures == 1..N
Colors == {"blue", "red", "yellow"}

VARIABLES creatureState, meetingPlace, meetingsTotal

vars == <<creatureState, meetingPlace, meetingsTotal>>

MeetingPairs(c, d) == IF c = d THEN {c} ELSE {c, d}

\* The complement rule: same colors stay unchanged; different colors both
\* become the third color.
Complement(c1, c2) ==
  IF c1 = c2 THEN LET col == c1[1] IN <<col, col>> ELSE
    LET col == CHOOSE z \in Colors : z # c1[1] /\ z # c2[1] IN <<col, col>>

TypeOK ==
  /\ creatureState \in [Creatures -> [color : Colors \cup {Faded}, participated : 0..M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ meetingsTotal \in 0..M

\* When the meeting place closes (the global counter hits M), no creature can
\* be left waiting in it: its sole occupant must have already faded out.
MeetingPlaceEmptyWhenFull ==
  (meetingsTotal = M) => (meetingPlace \in Creatures => creatureState[meetingPlace].color = Faded)

Init ==
  /\ creatureState \in [Creatures -> [color : Colors, participated : 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal = 0

EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ creatureState[c].color # Faded
  /\ meetingsTotal < M
  /\ meetingPlace' = c
  /\ UNCHANGED <<creatureState, meetingsTotal>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal = M
  /\ creatureState[c].color # Faded
  /\ creatureState' = [creatureState EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, meetingsTotal>>

MeetAndMutate(c) ==
  /\ meetingPlace \in Creatures
  /\ meetingPlace # c
  /\ creatureState[c].color # Faded
  /\ meetingsTotal < M
  /\ LET pair == MeetingPairs(c, meetingPlace) IN
       /\ creatureState' = [d \in Creatures |->
                              IF d \in pair
                                THEN LET mc == Complement(creatureState[c], creatureState[meetingPlace])
                                     IN [color |-> mc[1], participated |-> creatureState[d].participated + 1]
                                ELSE creatureState[d]]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ meetingsTotal' = meetingsTotal + 1

Next ==
  \/ \E c \in Creatures : EnterMeetingPlace(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  /\ meetingsTotal = M
  /\ (2 * M) = (creatureState[1].participated + creatureState[2].participated)

====