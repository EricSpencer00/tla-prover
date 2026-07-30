---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* The set of creatures, numbered 1..N.
Creatures == 1..N

Colors == {Meetings1, Meetings2, Faded}

VARIABLES color, place, met

vars == <<color, place, met>>

\* A creature has a color and a count of meetings it participated in; the meeting
\* place holds at most one waiting creature.
TypeOK ==
  /\ color \in [Creatures -> [c : Colors, count : 0..(M * 2)]]
  /\ place \in {MeetingPlaceEmpty} \cup Creatures
  /\ met \in 0..M

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN color[c].count + SumOver(S \ {c})

\* Safety: every meeting involves exactly two participants, so once the meeting
\* counter hits its maximum the individual counts sum to exactly twice that max.
SumMet == met = M => SumOver(Creatures) = 2 * M

Init ==
  /\ \E c \in [Creatures -> Colors] :
       /\ \A x \in Creatures : color[x].c = c[x]
       /\ \A x \in Creatures : color[x].count = 0
  /\ place = MeetingPlaceEmpty
  /\ met = 0

Enter(x) ==
  /\ place = MeetingPlaceEmpty
  /\ color[x].c # Faded
  /\ met < M
  /\ place' = x
  /\ UNCHANGED <<color, met>>

\* Latecomers fade out once the meeting place has closed.
FadeOut(x) ==
  /\ place = MeetingPlaceEmpty
  /\ met = M
  /\ color[x].c # Faded
  /\ color' = [color EXCEPT ![x].c = Faded]
  /\ UNCHANGED <<place, met>>

\* Two different creatures at the meeting place both adopt the color complement
\* of their pairwise colors.
MeetAndMutate(x) ==
  /\ place # MeetingPlaceEmpty
  /\ place # x
  /\ color[x].c # Faded
  /\ met < M
  /\ LET newColor ==
        IF color[x].c = color[place].c THEN color[x].c
        ELSE LET unused == {Meetings1, Meetings2, Faded} \ {color[x].c, color[place].c}
             IN CHOOSE y \in unused : TRUE
     IN /\ color' = [color EXCEPT ![x].c = newColor, ![place].c = newColor]
  /\ met' = met + 1
  /\ color' = [color EXCEPT ![x].count = @ + 1, ![place].count = @ + 1]
  /\ place' = MeetingPlaceEmpty

Next ==
  \/ \E x \in Creatures : Enter(x)
  \/ \E x \in Creatures : FadeOut(x)
  \/ \E x \in Creatures : MeetAndMutate(x)

Fairness ==
  /\ \A x \in Creatures : WF_vars(Enter(x))
  /\ \A x \in Creatures : WF_vars(FadeOut(x))
  /\ \A x \in Creatures : WF_vars(MeetAndMutate(x))

Spec == Init /\ [][Next]_vars /\ Fairness

====