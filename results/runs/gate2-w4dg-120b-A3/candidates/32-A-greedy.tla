---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a pair: its current color and its personal meeting count.
Creatures == [color : {"blue", "red", "yellow", Faded}, met : 0..M]
Occupants == 1..N

VARIABLES state, place, totalMet
vars == <<state, place, totalMet>>

RECURSIVE SumMet(_)
SumMet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN state[x].met + SumMet(S \ {x})

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF {c1, c2} = {"blue", "red"} THEN "yellow"
  ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
  ELSE "blue"

TypeOK ==
  /\ state \in [Occupants -> Creatures]
  /\ place \in Occupants \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0..M

Init ==
  /\ state = [o \in Occupants |-> [color |-> CHOOSE c \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
  /\ place = MeetingPlaceEmpty
  /\ totalMet = 0

Enter(o) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet < M
  /\ state[o].color # Faded
  /\ place' = o
  /\ UNCHANGED <<state, totalMet>>

Fade(o) ==
  /\ place = MeetingPlaceEmpty
  /\ totalMet = M
  /\ state[o].color # Faded
  /\ state' = [state EXCEPT ![o].color = Faded]
  /\ UNCHANGED <<place, totalMet>>

Meet(o) ==
  /\ place # MeetingPlaceEmpty
  /\ place # o
  /\ state[o].color # Faded
  /\ state[place].color # Faded
  /\ LET newc == Complement(state[o].color, state[place].color) IN
       state' = [state EXCEPT ![o].color = newc, ![place].color = newc,
                 ![o].met = @ + 1, ![place].met = @ + 1]
  /\ totalMet' = totalMet + 1
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E o \in Occupants : Enter(o)
  \/ \E o \in Occupants : Fade(o)
  \/ \E o \in Occupants : Meet(o)

Spec == Init /\ [][Next]_vars

SumMet == SumMet(Occupants)

\* When the meeting place has closed, every meeting is accounted for twice:
\* once in the global counter and once across the two participants.
SumMetMatchesGlobal ==
  totalMet = M => SumMet = 2 * M

====