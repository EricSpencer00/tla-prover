---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES color, met, meetingPlace, totalMet

vars == <<color, met, meetingPlace, totalMet>>

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

ColorComplement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET ss == ({"blue", "red", "yellow"} \ {c1, c2}) IN CHOOSE z \in ss : TRUE

TypeOK ==
  /\ color \in [Creatures -> Colors]
  /\ met \in [Creatures -> Nat]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0..M

Init ==
  /\ color \in [Creatures -> {"blue", "red", "yellow"}]
  /\ met = [c \in Creatures |-> 0]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ color[c] # Faded
  /\ totalMet < M
  /\ meetingPlace' = c
  /\ UNCHANGED <<color, met, totalMet>>

Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet >= M
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED <<met, meetingPlace, totalMet>>

Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ met[c] < M
  /\ met[meetingPlace] < M
  /\ LET mc == ColorComplement(color[c], color[meetingPlace]) IN
       color' = [color EXCEPT ![c] = mc, ![meetingPlace] = mc]
  /\ met' = [met EXCEPT ![c] = met[c] + 1, ![meetingPlace] = met[meetingPlace] + 1]
  /\ totalMet' = totalMet + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

SumMet == totalMet = M => SumOver(met, Creatures) = 2 * M

====