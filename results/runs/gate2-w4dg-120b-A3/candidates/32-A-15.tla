---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Colour alternatives before fading; each creature tracks its colour and how
\* many meetings it has taken part in. The shared counter counts meetings, not
\* participants.
VARIABLES cstate, occupant, global

vars == <<cstate, occupant, global>>

Colours == {"blue", "red", "yellow"}
Creatures == 0..(N - 1)
Unfaded == {c \in Creatures : cstate[c][1] # "faded"}

TotalCount ==
  LET sum[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN cstate[x][2] + sum[S \ {x}]
  IN sum[Creatures]

TypeOK ==
  /\ cstate \in [Creatures -> (Colours \cup {Faded}) \X (0..M)]
  /\ occupant \in Creatures \cup {MeetingPlaceEmpty}
  /\ global \in 0..M

Init ==
  /\ cstate = [c \in Creatures |->
        LET col == CHOOSE x \in Colours : TRUE IN <<col, 0>>]
  /\ occupant = MeetingPlaceEmpty
  /\ global = 0

Enter(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ global < M
  /\ cstate[c][1] # "faded"
  /\ occupant' = c
  /\ UNCHANGED <<cstate, global>>

Fade(c) ==
  /\ occupant = MeetingPlaceEmpty
  /\ global = M
  /\ cstate[c][1] # "faded"
  /\ cstate' = [cstate EXCEPT ![c] = <<"faded", cstate[c][2]>>]
  /\ UNCHANGED <<occupant, global>>

Complement(c, d) ==
  /\ occupant # MeetingPlaceEmpty
  /\ occupant # c
  /\ c \in Unfaded
  /\ occupant \in Unfaded
  /\ LET col1 == cstate[c][1]
         col2 == cstate[occupant][1]
         newcol == IF col1 = col2 THEN col1
                  ELSE {x \in Colours : x # col1 /\ x # col2}[1]
     IN /\ cstate' = [cstate EXCEPT
            ![c] = <<newcol, cstate[c][2] + 1>>,
            ![occupant] = <<newcol, cstate[occupant][2] + 1>>]
        /\ global' = global + 1
        /\ occupant' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Complement(c, occupant)

Spec == Init /\ [][Next]_vars

SumMet == global = M => TotalCount = 2 * M

====