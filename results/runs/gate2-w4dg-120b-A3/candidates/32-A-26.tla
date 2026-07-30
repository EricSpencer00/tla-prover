---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creature == 0 .. (N - 1)
Color == {"blue", "red", "yellow", Faded}

VARIABLES status, occupant, total
vars == <<status, occupant, total>>

TotalMeetings == 2 * M

\* The complement rule is given as a separate function because the invariants
\* do not name it directly, but every meeting must resolve it exactly once.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET cs == {"blue", "red", "yellow"} IN (cs \ {c1, c2})[1]

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

TypeOK ==
  /\ status \in [Creature -> [color : Color, met : 0..TotalMeetings]]
  /\ occupant \in Creature \cup {MeetingPlaceEmpty}
  /\ total \in 0..TotalMeetings

Init ==
  /\ status = [c \in Creature |-> [color |-> CHOOSE col \in {"blue", "red", "yellow"} : TRUE, met |-> 0]]
  /\ occupant = MeetingPlaceEmpty
  /\ total = 0

EnterEmpty(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ total < M
  /\ status[c].color # Faded
  /\ occupant' = c
  /\ UNCHANGED <<status, total>>

FadeOut(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ total >= M
  /\ status[c].color # Faded
  /\ status' = [status EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<occupant, total>>

\* The arriving chimp meets the waiting one, then the place empties.
MeetAndMutate(c) ==
  /\ occupant # MeetingPlaceEmpty
  /\ occupant # c
  /\ status[c].color # Faded
  /\ total < M
  /\ LET nc == Complement(status[occupant].color, status[c].color) IN
       status' = [status EXCEPT ![c].color = nc, ![occupant].color = nc, ![c].met = @ + 1, ![occupant].met = @ + 1]
  /\ total' = total + 1
  /\ occupant' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creature : EnterEmpty(c)
  \/ \E c \in Creature : FadeOut(c)
  \/ \E c \in Creature : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == total >= M => SumOf([c \in Creature |-> status[c].met], Creature) = TotalMeetings

====