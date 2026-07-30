---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is either faded or one of M colors, indexed 1..M.
Colors == 1..M

\* The per-creature record: current color (or Faded) and how many meetings
\* that creature has participated in.
CreatureRec == [col : Colors \cup {Faded}, participated : 0..M]

VARIABLES creatureState, meetingPlace, total

vars == <<creatureState, meetingPlace, total>>

\* Color complement: two creatures keep their color if it matches, otherwise
\* both adopt the third color not held by either.
Complement(c, d) ==
  IF c = d THEN c
  ELSE LET colors == {c, d, 1, 2, 3} IN CHOOSE e \in colors : e # c /\ e # d

\* Total meetings is the sum of individual participation counts.
RECURSIVE Tally(_)
Tally(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN creatureState[x].participated + Tally(S \ {x})

Init ==
  /\ creatureState = [c \in 1..N |-> [col |-> 1, participated |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total = 0

\* Enter: a non-faded creature takes the free meeting place while meetings
\* remain below the limit.
Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total < N
  /\ creatureState[c].col # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<creatureState, total>>

\* Fade: with the place closed and an empty slot, a creature that tries to
\* enter simply becomes faded.
Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total >= N
  /\ creatureState[c].col # Faded
  /\ creatureState' = [creatureState EXCEPT ![c].col = Faded]
  /\ UNCHANGED <<meetingPlace, total>>

\* Meet: two distinct creatures occupy the place and both pick up a new
\* color; two participation counts and the global counter all advance.
Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ creatureState[c].col # Faded
  /\ creatureState' = [x \in 1..N |->
        IF x = c THEN
          [col |-> Complement(creatureState[meetingPlace].col, creatureState[c].col),
           participated |-> creatureState[c].participated + 1]
        ELSE IF x = meetingPlace THEN
          [col |-> Complement(creatureState[meetingPlace].col, creatureState[c].col),
           participated |-> creatureState[meetingPlace].participated + 1]
        ELSE creatureState[x]]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ total' = total + 1

Next ==
  \/ \E c \in 1..N : Enter(c) \/ Fade(c) \/ Meet(c)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E c \in 1..N : Enter(c))
  /\ WF_vars(\E c \in 1..N : Meet(c))
  /\ SF_vars(\E c \in 1..N : Fade(c))

TypeOK ==
  /\ creatureState \in [1..N -> CreatureRec]
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in 0..N

\* Every meeting involves two participants, so at the moment the place closes
\* the running total of individual participations is exactly twice the number
\* of meetings that have occurred.
SumMet ==
  (total = N) => (Tally(1..N) = 2 * N)

====