---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature colors: blue, red, yellow, plus the faded final state.
Colors == {"blue", "red", "yellow", Faded}

\* The color complement rule: if two creatures have the same color they keep
\* it; otherwise both adopt the third color not held by either.
Complement(c, d) ==
  IF c = d THEN c
  ELSE LET S == {"blue", "red", "yellow"} \ {c, d} IN CHOOSE e \in S : TRUE

Individuals == 1 .. N

VARIABLES palette, meetingPlace, meetings

vars == <<palette, meetingPlace, meetings>>

TypeOK ==
  /\ palette \in [Individuals -> [color: Colors, met: 0 .. M]]
  /\ meetingPlace \in Individuals \cup {MeetingPlaceEmpty}
  /\ meetings \in 0 .. M

Init ==
  /\ \E f \in [Individuals -> Colors]: palette = [i \in Individuals |-> [color |-> f[i], met |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetings = 0

AnyoneFaded == \E i \in Individuals : palette[i].color = Faded

\* A creature may enter the meeting place only while it is empty and the
\* meeting budget has not been spent.
Enter(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetings < M
  /\ palette[i].color # Faded
  /\ meetingPlace' = i
  /\ UNCHANGED <<palette, meetings>>

\* Fading out is only enabled once the meeting place is closed, so it can only
\* ever happen after the budget is spent.
FadeOut(i) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetings = M
  /\ palette[i].color # Faded
  /\ palette' = [palette EXCEPT ![i].color = Faded]
  /\ UNCHANGED <<meetingPlace, meetings>>

\* A meeting mutates both creatures' colors at once and charges both sides.
Meet(i) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # i
  /\ palette[i].color # Faded
  /\ palette' = [j \in Individuals |->
        IF j = i \/ j = meetingPlace
          THEN [color |-> Complement(palette[i].color, palette[meetingPlace].color), met |-> palette[j].met + 1]
          ELSE palette[j]]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ meetings' = meetings + 1

Next ==
  \/ \E i \in Individuals : Enter(i)
  \/ \E i \in Individuals : FadeOut(i)
  \/ \E i \in Individuals : Meet(i)

Spec == Init /\ [][Next]_vars

\* An invariant statement, so the LIVENESS clause stays empty in the config.
SumMet ==
  LET f[S \in SUBSET Individuals] ==
       IF S = {} THEN 0
       ELSE LET c == CHOOSE x \in S : TRUE IN palette[c].met + f[S \ {c}]
  IN f[Individuals]

====