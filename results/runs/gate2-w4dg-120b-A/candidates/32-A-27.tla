---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by numbers 1..N. Each creature's state is a pair
\* <color, meetingsParticipated>, so the meeting counts are always available.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES chState, meetingPlace, totalMeetings
vars == <<chState, meetingPlace, totalMeetings>>

TypeOK ==
  /\ chState \in [Creatures -> [col : Colors, cnt : 0..M]]
  /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
  /\ totalMeetings \in 0..M

\* Sum of individual participation counts (twice the number of meetings).
RECURSIVE SumFn(_)
SumFn(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN chState[c].cnt + SumFn(S \ {c})
SumMet == SumFn(Creatures) = 2 * totalMeetings

\* The complement rule: same color stays, different colors become the third.
Complement(c1, c2) ==
  LET col1 == chState[c1].col
      col2 == chState[c2].col
  IN IF col1 = col2 THEN col1
     ELSE LET cand == {"blue", "red", "yellow"} \ {col1, col2}
          IN CHOOSE x \in cand : TRUE

Init ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0
  /\ \E f \in [Creatures -> Colors]:
       /\ totalMeetings = 0
       /\ \A c \in Creatures: chState[c] = [col |-> f[c], cnt |-> 0]

EnterPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ chState[c].col # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<chState, totalMeetings>>

\* Fading is the terminal path: no meeting place to join, so a creature
\* that would join instead drops out, keeping its own meeting count.
FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ chState[c].col # Faded
  /\ chState' = [chState EXCEPT ![c].col = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* A real meeting: two distinct creatures, both recolored together, both
\* credited with participation, and the meeting place cleared.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ chState[c].col # Faded
  /\ LET newcol == Complement(c, meetingPlace)
     IN chState' = [chState EXCEPT ![c] = [col |-> newcol, cnt |-> @ + 1],
                                ![meetingPlace] = [col |-> newcol, cnt |-> @ + 1]]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures: EnterPlace(c)
  \/ \E c \in Creatures: FadeOut(c)
  \/ \E c \in Creatures: MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

====