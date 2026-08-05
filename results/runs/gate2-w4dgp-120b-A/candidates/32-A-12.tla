---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow"}

VARIABLES color, met, meetingPlace, totalMet

vars == <<color, met, meetingPlace, totalMet>>

\* The complement of two colors under the chameneos rule.
Complement(a, b) ==
  IF a = b
  THEN a
  ELSE LET c == {"blue", "red", "yellow"} \ {a, b} IN CHOOSE x \in c : TRUE

RECURSIVE SumOver(_)
SumOver(S) ==
  IF S = {}
  THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN met[c] + SumOver(S \ {c})

InitialColors == CHOOSE f \in [Creatures -> Colors] :
  \A g \in Creatures : (g = 0) \/ (f[g] # f[g - 1])

TypeOK ==
  /\ color \in [Creatures -> Colors \cup {Faded}]
  /\ met \in [Creatures -> 0 .. M]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMet \in 0 .. M

Init ==
  /\ color = InitialColors
  /\ met = [c \in Creatures |-> 0]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = 0

EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet < M
  /\ color[c] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<color, met, totalMet>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMet = M
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED <<met, meetingPlace, totalMet>>

Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Complement(color[c], color[meetingPlace]), ![meetingPlace] = Complement(color[c], color[meetingPlace])]
  /\ met' = [met EXCEPT ![c] = @ + 1, ![meetingPlace] = @ + 1]
  /\ totalMet' = totalMet + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterMeetingPlace(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  (totalMet = M) => (SumOver(Creatures) = 2 * M)

====