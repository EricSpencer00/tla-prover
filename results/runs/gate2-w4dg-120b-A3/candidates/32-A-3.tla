---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Colors is the set of all colors a creature can hold, including the faded
\* terminal marker.
Colors == {"blue", "red", "yellow"} \cup {Faded}

Creatures == 1 .. N

VARIABLES cstate, place, global

vars == <<cstate, place, global>>

\* Complement rule: the set of colors apart from the two arguments.
ThirdOf(e1, e2) ==
  LET seen == {e1, e2} IN
    CHOOSE c \in Colors \ seen : TRUE

Bump(n) == IF n < M THEN n + 1 ELSE n

TypeOK ==
  /\ cstate \in [Creatures -> Colors \X 0..M]
  /\ place \in Creatures \cup {MeetingPlaceEmpty}
  /\ global \in 0..M

Init ==
  /\ cstate \in [Creatures -> (Colors \ {Faded}) \X {0}]
  /\ place = MeetingPlaceEmpty
  /\ global = 0

EnterPlace(i) ==
  /\ place = MeetingPlaceEmpty
  /\ cstate[i][1] # Faded
  /\ global < M
  /\ place' = i
  /\ UNCHANGED <<cstate, global>>

FadeOut(i) ==
  /\ place = MeetingPlaceEmpty
  /\ cstate[i][1] # Faded
  /\ global = M
  /\ cstate' = [cstate EXCEPT ![i] = <<Faded, cstate[i][2]>>]
  /\ UNCHANGED <<place, global>>

MeetAndMutate(i) ==
  /\ place # MeetingPlaceEmpty
  /\ i # place
  /\ cstate[i][1] # Faded
  /\ LET c' == ThirdOf(cstate[i][1], cstate[place][1]) IN
       /\ cstate' = [cstate EXCEPT ![i] = <<c', Bump(cstate[i][2])>>, ![place] = <<c', Bump(cstate[place][2])>>]
  /\ place' = MeetingPlaceEmpty
  /\ global' = IF global < M THEN global + 1 ELSE global

Next ==
  \/ \E i \in Creatures : EnterPlace(i)
  \/ \E i \in Creatures : FadeOut(i)
  \/ \E i \in Creatures : MeetAndMutate(i)

Spec == Init /\ [][Next]_vars

\* When the global meeting counter is saturated, individual meeting counts sum
\* to exactly twice that many meetings -- each meeting recorded for both participants.
SumMet ==
  Global = M => LET f[S \in SUBSET Creatures] ==
    IF S = {} THEN 0
    ELSE LET c \in S IN cstate[c][2] + f[S \ {c}]
  IN f[Creatures] = 2 * M

====