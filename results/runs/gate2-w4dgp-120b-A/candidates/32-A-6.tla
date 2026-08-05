---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A small pool of creatures that share a single meeting place ("the Mall").
\* Two creatures meeting is a pairwise event: both participants' meeting counts
\* go up, the global meeting counter goes up, and the Mall empties again.
\* Once the total number of meetings M has been reached the Mall closes and any
\* creature trying to enter instead fades out (its color becomes Faded). The
\* safety property checks that no meeting is ever counted under only one
\* participant: the sum of all individual counts must be exactly twice the
\* total number of meetings, since each meeting contributes one to two creatures.
\* The model is bounded: the number of creatures and the meeting limit M are
\* fixed constants, not the size of an unbounded population.

Creatures == 0 .. (N - 1)

Colors == {"blue", "red", "yellow"}

VARIABLES cstate, meetingPlace, totalMet

vars == <<cstate, meetingPlace, totalMet>>

TypeOK ==
  /\ cstate \in [Creatures -> [color : Colors \cup {Faded}, met : Nat]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in Nat

\* The complement rule: two creatures meeting always come away with the same
\* color, which is either their shared input color or the third color in the set.
Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE (CHOOSE c \in Colors : c # c1 /\ c # c2)

Init ==
  /\ cstate = [c \in Creatures |-> [color |-> CHOOSE c \in Colors : TRUE, met |-> 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

\* A creature joins the empty Mall when meetings are still available.
Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet < M
  /\ cstate[c].color # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<cstate, totalMet>>

\* Once the meeting limit is reached, a creature trying to enter simply fades.
Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = M
  /\ cstate[c].color # Faded
  /\ cstate' = [cstate EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMet>>

\* Two distinct creatures meet and both adopt the complement color.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ cstate[meetingPlace].color # Faded
  /\ cstate[c].color # Faded
  /\ LET newcolor == Complement(cstate[meetingPlace].color, cstate[c].color) IN
       cstate' = [cstate EXCEPT ![meetingPlace].color = newcolor, ![c].color = newcolor,
                  ![meetingPlace].met = @ + 1, ![c].met = @ + 1]
  /\ totalMet' = totalMet + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == totalMet = M => (cstate[0].met + cstate[1].met) = (2 * M)

====