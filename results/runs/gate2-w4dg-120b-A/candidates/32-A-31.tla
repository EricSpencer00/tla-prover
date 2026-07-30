---- MODULE Chameneos ----
EXTENDS Naturals

\* A chameneos concurrency game. Each creature carries a color and a meeting
\* count. Two creatures meet at a shared meeting place (the "mall"): entering
\* the place, meeting, and mutating both colors together. A global counter
\* limits how many meetings happen; once it saturates, the place closes and
\* creatures fade out. The total number of individual creature participations
\* is always exactly twice the number of completed meetings (each meeting
\* counts once for each of its two participants).

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow"}
ColorOf == [c \in Creatures |-> CHOOSE x \in Colors : TRUE]

VARIABLES pool, mall, meetings
vars == <<pool, mall, meetings>>

RECURSIVE SumFun(_, _)
SumFun(f, S) == IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE
                     IN f[x] + SumFun(f, S \ {x})

TypeOK ==
  /\ pool \in [Creatures -> [color: Colors \cup {Faded}, met: 0..M]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ meetings \in 0..M

Init ==
  /\ pool = [c \in Creatures |-> [color |-> ColorOf[c], met |-> 0]]
  /\ mall = MeetingPlaceEmpty
  /\ meetings = 0

Clarity == IF pool[a].color = pool[b].color
           THEN pool[a].color
           ELSE LET base == {pool[a].color, pool[b].color}
                IN CHOOSE x \in Colors : x \notin base

Enter(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ pool[c].color # Faded
  /\ meetings < M
  /\ mall' = c
  /\ pool' = pool
  /\ meetings' = meetings

FadeOut(c) ==
  /\ mall = MeetingPlaceEmpty
  /\ pool[c].color # Faded
  /\ meetings = M
  /\ pool' = [pool EXCEPT ![c].color = Faded]
  /\ mall' = mall
  /\ meetings' = meetings

MeetAndMutate(c) ==
  /\ mall \in Creatures
  /\ mall # c
  /\ pool[c].color # Faded
  /\ pool[mall].color # Faded
  /\ meetings < M
  /\ LET newcol == Clarity(c, mall) IN
       pool' = [pool EXCEPT ![c].color = newcol, ![mall].color = newcol,
                          ![c].met = @ + 1, ![mall].met = @ + 1]
  /\ mall' = MeetingPlaceEmpty
  /\ meetings' = meetings + 1

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == SumFun([c \in Creatures |-> pool[c].met], Creatures)

\* Bounded capacity: the summed meeting participation across all creatures
\* is exactly twice the global meeting count at saturation.
MeetingsAccounted ==
  meetings = M => SumMet = 2 * M

====