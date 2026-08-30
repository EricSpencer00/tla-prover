---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Each creature is identified by an integer 1..N (0 being unused); the model
\* tracks each creature's color and its own meeting count, plus the global
\* meeting counter and a single-slot meeting place.
Creatures == 1..N

VARIABLES state, mallSlot, globalCount

vars == <<state, mallSlot, globalCount>>

Colors == {"blue", "red", "yellow", Faded}

\* Sum of the individual meeting counts; it equals twice the number of meetings
\* because each meeting involves exactly two participants.
RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN state[x][2] + SumOver(S \ {x})

TypeOK ==
  /\ state \in [Creatures -> [color: Colors, count: 0..M]]
  /\ mallSlot \in Creatures \cup {MeetingPlaceEmpty}
  /\ globalCount \in 0..M

Init ==
  /\ state \in [Creatures -> [color: {"blue", "red", "yellow"}, count: 0..M]]
  /\ mallSlot = MeetingPlaceEmpty
  /\ globalCount = 0

\* A creature enters the meeting place to wait for a partner; the place holds
\* at most one waiting creature at a time.
EnterEmpty(c) ==
  /\ mallSlot = MeetingPlaceEmpty
  /\ state[c].color # Faded
  /\ globalCount < M
  /\ mallSlot' = c
  /\ UNCHANGED <<state, globalCount>>

FadeOut(c) ==
  /\ mallSlot = MeetingPlaceEmpty
  /\ globalCount >= M
  /\ state[c].color # Faded
  /\ state' = [state EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<mallSlot, globalCount>>

\* The meeting: both participants adopt the complement of their colors and each
\* record one more meeting in their own count and the global count.
Meet(c) ==
  /\ mallSlot # MeetingPlaceEmpty
  /\ mallSlot # c
  /\ globalCount < M
  /\ LET newcol == IF state[c].color = state[mallSlot].color
                  THEN state[c].color
                  ELSE CHOOSE x \in Colors \ {"Faded", state[c].color, state[mallSlot].color} : TRUE
     IN state' = [state EXCEPT ![c].color = newcol, ![c].count = @ + 1,
                                ![mallSlot].color = newcol, ![mallSlot].count = @ + 1]
  /\ globalCount' = globalCount + 1
  /\ mallSlot' = MeetingPlaceEmpty

Next ==
  \E c \in Creatures : EnterEmpty(c) \/ FadeOut(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* At most M meetings happen total, and the per-creature counts add up to
\* exactly twice the global count, which holds only if every meeting touched two
\* distinct participants (never self-meeting, never a lost update).
SumMet == globalCount = M => SumOver(Creatures) = 2 * M

====