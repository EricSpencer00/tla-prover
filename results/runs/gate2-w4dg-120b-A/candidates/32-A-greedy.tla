---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a pair: its current color and its personal meeting count.
Creatures == [1..N -> [color : {"blue", "red", "yellow", Faded}, met : 0..M]]
Colors == {"blue", "red", "yellow"}

VARIABLES creatures, meetingPlace, totalMet

vars == <<creatures, meetingPlace, totalMet>>

RECURSIVE SumMet(_)
SumMet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN creatures[x].met + SumMet(S \ {x})

TypeOK ==
  /\ creatures \in Creatures
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0..M

Init ==
  /\ \E f \in [1..N -> Colors] :
       creatures = [i \in 1..N |-> [color |-> f[i], met |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

Enter(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet < M
  /\ creatures[i].color # Faded
  /\ meetingPlace' = i
  /\ UNCHANGED <<creatures, totalMet>>

FadeOut(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = M
  /\ creatures[i].color # Faded
  /\ creatures' = [creatures EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMet>>

\* The complement rule: same colors stay, different colors become the third.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET x \in Colors : x # c1 /\ x # c2 IN x

Meet(i) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # i
  /\ creatures[i].color # Faded
  /\ creatures[meetingPlace].color # Faded
  /\ LET nc == Complement(creatures[i].color, creatures[meetingPlace].color) IN
       /\ creatures' = [creatures EXCEPT ![i].color = nc, ![meetingPlace].color = nc]
  /\ creatures' = [creatures EXCEPT ![i].met = @ + 1, ![meetingPlace].met = @ + 1]
  /\ totalMet' = totalMet + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E i \in 1..N : Enter(i)
  \/ \E i \in 1..N : FadeOut(i)
  \/ \E i \in 1..N : Meet(i)

Spec == Init /\ [][Next]_vars

SumMet == SumMet(1..N)

\* When the meeting place has closed, the per-creature counts add up to twice
\* the number of meetings, since each meeting involved exactly two participants.
MeetingCountMatches == totalMet = M => SumMet = 2 * M

====