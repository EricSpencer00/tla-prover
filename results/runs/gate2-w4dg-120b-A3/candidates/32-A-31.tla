---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creature ids are the natural numbers 1..N
Creatures == 1..N
Colors == {"blue", "red", "yellow"}
Complement == [x \in Colors \cup {Faded}, y \in Colors \cup {Faded} |-> IF x = y THEN x
                     ELSE CHOOSE z \in Colors : z # x /\ z # y]

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

VARIABLES state, meetingPlace, total
vars == <<state, meetingPlace, total>>

TypeOK ==
  /\ state \in [Creatures -> (Colors \cup {Faded}) \X (0..M)]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in 0..M

Init ==
  /\ \E c \in [Creatures -> Colors]: state = [k \in Creatures |-> <<c[k], 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total = 0

Enter(k) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total < M
  /\ state[k][1] # Faded
  /\ meetingPlace' = k
  /\ UNCHANGED <<state, total>>

Fade(k) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ total = M
  /\ state[k][1] # Faded
  /\ state' = [state EXCEPT ![k][1] = Faded]
  /\ UNCHANGED <<meetingPlace, total>>

Meet(k) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ k # meetingPlace
  /\ LET c1 == state[k][1] /\ c2 == state[meetingPlace][1]
         nc == Complement[c1][c2]
     IN /\ state' = [state EXCEPT ![k] = <<nc, @.2 + 1>>, ![meetingPlace] = <<nc, @.2 + 1>>]
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ total' = total + 1

Next == \E k \in Creatures: Enter(k) \/ Fade(k) \/ Meet(k)

Spec == Init /\ [][Next]_vars

SumMet == total = M => SumOf([k \in Creatures |-> state[k][2]], Creatures) = 2 * M

====