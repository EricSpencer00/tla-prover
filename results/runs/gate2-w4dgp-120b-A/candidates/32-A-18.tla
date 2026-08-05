---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A chameneos of the forest gathers at a single meeting place (the Mall).
\* Two chameneos meeting together both change color according to a
\* complementation rule. Only a fixed total number of meetings are allowed;
\* once that limit is reached the meeting place closes and chameneos that
\* try to enter simply fade out. The invariant checks that the per-creature
\* meeting counts sum to exactly twice the total number of meetings, because
\* every meeting involves exactly two participants.

Creatures == 1..N

Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, place, total

vars == <<state, place, total>>

TypeOK ==
  /\ state \in [Creatures -> [color : Colors, ment : 0..M]]
  /\ place \in (Creatures \cup {MeetingPlaceEmpty})
  /\ total \in 0..M

RECURSIVE SumMet(_)
SumMet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE e \in S : TRUE IN state[x].ment + SumMet(S \ {x})

Init ==
  /\ \E f \in [Creatures -> Colors \ {Faded}] :
       state = [c \in Creatures |-> [color |-> f[c], ment |-> 0]]
  /\ place = MeetingPlaceEmpty
  /\ total = 0

\* A chameneos that is not already at the meeting place enters it, provided
\* the place is empty and the total-meeting budget has not been spent.
Enter(c) ==
  /\ place = MeetingPlaceEmpty
  /\ state[c].color # Faded
  /\ total < M
  /\ place' = c
  /\ UNCHANGED <<state, total>>

\* With the meeting budget spent, a chameneos that still tries to enter
\* simply fades out.
FadeOut(c) ==
  /\ place = MeetingPlaceEmpty
  /\ state[c].color # Faded
  /\ total = M
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<place, total>>

\* The complement rule: if both chameneos are the same color they keep it;
\* otherwise they both take the third color not held by either.
Complement(a, b) ==
  IF state[a].color = state[b].color THEN state[a].color
  ELSE LET {c1, c2} == {state[a].color, state[b].color} IN
       CHOOSE k \in {"blue", "red", "yellow"} : k \notin {c1, c2}

\* Two different chameneos meet at the meeting place, both adopt the
\* complementary color and both count one more meeting.
Meet(c) ==
  /\ place # MeetingPlaceEmpty
  /\ c # place
  /\ total < M
  /\ state' = [state EXCEPT ![c].color = Complement(c, place), ![c].ment = @ + 1,
                              ![place].color = Complement(c, place), ![place].ment = @ + 1]
  /\ total' = total + 1
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

\* Every meeting touches exactly two participants, so the sum of the
\* per-creature meeting counts equals twice the number of meetings.
SumMet == total = M => SumMet(Creatures) = 2 * M

====