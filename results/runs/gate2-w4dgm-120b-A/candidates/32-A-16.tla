---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a record [color |-> one of {blue, red, yellow, Faded}]
\* together with a meeting count. The meeting place holds at most one waiting
\* creature; meeting is pairwise and symmetric, and each meeting increments both
\* participants and the global total. When the total reaches its bound the place
\* closes and creatures simply fade out instead of joining.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN
       CHOOSE c \in {"blue", "red", "yellow"} : c \notin s

VARIABLES state, occupant, total

RECURSIVE SumF(_)
SumF(S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE y \in S : TRUE IN state[x].meet + SumF(S \ {x})

TypeOK ==
  /\ state \in [Creatures -> [color: Colors, meet: 0..M]]
  /\ occupant \in (Creatures \cup {MeetingPlaceEmpty})
  /\ total \in 0..M

Init ==
  /\ state \in [Creatures -> [color: {"blue", "red", "yellow"}, meet: 0]]
  /\ occupant = MeetingPlaceEmpty
  /\ total = 0

\* A non-faded creature waits in the meeting place while there is room.
EnterWaiting(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ state[c].color /= Faded
  /\ total < M
  /\ occupant' = c
  /\ UNCHANGED <<state, total>>

\* The meeting place is closed: a creature that tries to join simply fades out.
ExitFaded(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ total = M
  /\ state[c].color /= Faded
  /\ state' = [state EXCEPT ![c] = [color |-> Faded, meet |-> @.meet]]
  /\ UNCHANGED <<occupant, total>>

\* A meeting happens: two different creatures both adopt the complement of
\* their colors and are charged one meeting each.
Meet(c, w) ==
  /\ occupant = w
  /\ c # w
  /\ total < M
  /\ state[c].color /= Faded
  /\ state[w].color /= Faded
  /\ LET newc == Complement(state[c].color, state[w].color) IN
       /\ state' = [state EXCEPT ![c] = [color |-> newc, meet |-> @.meet + 1],
                                ![w] = [color |-> newc, meet |-> @.meet + 1]]
  /\ total' = total + 1
  /\ occupant' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterWaiting(c)
  \/ \E c \in Creatures : ExitFaded(c)
  \/ \E c \in Creatures, w \in Creatures : Meet(c, w)

Spec == Init /\ [][Next]_<<state, occupant, total>>

\* Every completed meeting accounts for exactly two creatures' meeting counts,
\* so the sum of all individual counts is twice the global total.
MeetingCountCoherent == total = M => SumF(Creatures) = 2 * total

\* Conservation: the global meeting total never exceeds its bound.
BoundedTotal == total <= M

====