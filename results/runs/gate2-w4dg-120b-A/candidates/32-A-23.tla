---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N

Colors == {"blue", "red", "yellow", Faded}
BaseColors == {"blue", "red", "yellow"}

VARIABLES state, place, totalMeetings

vars == << state, place, totalMeetings >>

\* state[c] = << the creature's current color (or faded), the number of
\* meetings c has participated in >>.
\* place = occupant of the meeting place, or MeetingPlaceEmpty.
\* totalMeetings = total meetings that have occurred system-wide.
RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN state[c][2] + SumOf(S \ {c})

Complement(c1, c2) ==
  IF state[c1][1] = state[c2][1] THEN state[c1][1]
  ELSE LET missing == CHOOSE col \in BaseColors : col # state[c1][1] /\ col # state[c2][1]
       IN missing

TypeOK ==
  /\ state \in [Creatures -> [Colors \X (0..M)]]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

InitialColors ==
  { f \in [Creatures -> Colors] : \A c \in Creatures : f[c] \in BaseColors }

Init ==
  /\ state \in InitialColors
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* A creature enters the empty meeting place to wait for a partner.
Enter(c) ==
  /\ place = MeetingPlaceEmpty
  /\ state[c][1] # Faded
  /\ totalMeetings < M
  /\ place' = c
  /\ UNCHANGED << state, totalMeetings >>

\* When the meeting place has closed, a creature that tries to enter fades out
\* rather than waiting, keeping its meeting count.
FadeOut(c) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ state[c][1] # Faded
  /\ state' = [state EXCEPT ![c][1] = Faded]
  /\ UNCHANGED << place, totalMeetings >>

\* Two distinct creatures meet and both adopt the complement of their colors.
Meet(c) ==
  /\ place # MeetingPlaceEmpty
  /\ place # c
  /\ state[c][1] # Faded
  /\ state[place][1] # Faded
  /\ LET newcol == Complement(c, place) IN
       state' = [state EXCEPT ![c] = << newcol, @ [2] + 1 >>, ![place] = << newcol, @ [2] + 1 >>]
  /\ totalMeetings' = totalMeetings + 1
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* At the meeting limit, every meeting's two participants are fully accounted
\* for in the individual meeting counts.
SumMet == totalMeetings = M => SumOf(Creatures) = 2 * M

====