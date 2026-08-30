---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME /\ N \in Nat /\ N >= 1
       /\ M \in Nat /\ M >= 1
       /\ Faded \notin {"blue", "red", "yellow"}
       /\ MeetingPlaceEmpty \notin (1 .. N)

Colors == {"blue", "red", "yellow"}

VARIABLES state, place, totalMeetings

vars == <<state, place, totalMeetings>>

TypeOK ==
  /\ state \in [1 .. N -> [color: Colors \cup {Faded}, met: 0 .. M]]
  /\ place \in (1 .. N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0 .. M

Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

SumMet == Sum([k \in 1 .. N |-> state[k].met], 1 .. N)

Init ==
  /\ state = [k \in 1 .. N |-> [color |-> CHOOSE c \in Colors : TRUE, met |-> 0]]
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterPlace(k) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ state[k].color # Faded
  /\ place' = k
  /\ UNCHANGED <<state, totalMeetings>>

FadeOut(k) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ state[k].color # Faded
  /\ state' = [state EXCEPT ![k].color = Faded]
  /\ UNCHANGED <<place, totalMeetings>>

\* Complement rule: equal colors stay; unequal colors both become the third.
Complement(a, b) ==
  IF a = b THEN a
  ELSE (CHOOSE c \in Colors : c # a /\ c # b)

MeetAndMutate(k) ==
  /\ place # MeetingPlaceEmpty
  /\ k # place
  /\ totalMeetings < M
  /\ LET newColor == Complement(state[k].color, state[place].color)
     IN state' = [state EXCEPT ![k].color = newColor,
                               ![k].met = state[k].met + 1,
                               ![place].color = newColor,
                               ![place].met = state[place].met + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E k \in 1 .. N : EnterPlace(k) \/ FadeOut(k) \/ MeetAndMutate(k)

Spec == Init /\ [][Next]_vars

\* Bounded capacity: the global meeting counter must account for every
\* individual creature having participated exactly twice when it saturates.
MeetingCapacityRespected == totalMeetings = M => SumMet = 2 * M

====