---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0

Creatures == 1..N

\* The complement rule: a meeting of unequal colors yields the third one.
Complement(a, b) == IF a = b THEN a
                     ELSE CASE a = "blue" /\ b = "red" : "yellow"
                           [] a = "red" /\ b = "blue" : "yellow"
                           [] a = "blue" /\ b = "yellow" : "red"
                           [] a = "yellow" /\ b = "blue" : "red"
                           [] a = "red" /\ b = "yellow" : "blue"
                           [] a = "yellow" /\ b = "red" : "blue"

RECURSIVE CountTotal(_, _)
CountTotal(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + CountTotal(f, S \ {x})

VARIABLES color, participantCount, meetingPlace, totalMeetings

vars == <<color, participantCount, meetingPlace, totalMeetings>>

TypeOK ==
  /\ color \in [Creatures -> {Faded, "blue", "red", "yellow"}]
  /\ participantCount \in [Creatures -> Nat]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ \E g \in [Creatures -> {Faded, "blue", "red", "yellow"}] :
        /\ \A c \in Creatures : g[c] # Faded
        /\ color' = g
  /\ participantCount' = [c \in Creatures |-> 0]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = 0

EnterPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ color[c] # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = c
  /\ UNCHANGED <<color, participantCount, totalMeetings>>

Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ color[c] # Faded
  /\ color' = [color EXCEPT ![c] = Faded]
  /\ UNCHANGED <<participantCount, meetingPlace, totalMeetings>>

Meet(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ color[c] # Faded
  /\ color[meetingPlace] # Faded
  /\ LET newColor == Complement(color[c], color[meetingPlace]) IN
        /\ color' = [color EXCEPT ![c] = newColor, ![meetingPlace] = newColor]
  /\ participantCount' = [participantCount EXCEPT ![c] = @ + 1, ![meetingPlace] = @ + 1]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterPlace(c)
  \/ \E c \in Creatures : Fade(c)
  \/ \E c \in Creatures : Meet(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  (totalMeetings = M) => (CountTotal(participantCount, Creatures) = 2 * M)

====