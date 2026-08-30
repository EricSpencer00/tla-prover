---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0

Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}

\* The third color distinct from the two given ones.
Third(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE IF (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") THEN "yellow"
  ELSE IF (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") THEN "red"
  ELSE "blue"

VARIABLES status, meetingPlace, totalMeetings

vars == << status, meetingPlace, totalMeetings >>

InitStatus ==
  [c \in Creatures |-> [color |-> CHOOSE k \in Colors : k # Faded, count |-> 0]]

TypeOK ==
  /\ status \in [Creatures -> [color : Colors, count : 0..M]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ status = InitStatus
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterEmpty(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ status[c].color # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = c
  /\ UNCHANGED << status, totalMeetings >>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ status[c].color # Faded
  /\ totalMeetings >= M
  /\ status' = [status EXCEPT ![c].color = Faded]
  /\ UNCHANGED << meetingPlace, totalMeetings >>

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ c # meetingPlace
  /\ status[c].color # Faded
  /\ totalMeetings < M
  /\ status' = [status EXCEPT ![c] = [color |-> Third(status[c].color, status[meetingPlace].color), count |-> status[c].count + 1],
                               ![meetingPlace] = [color |-> Third(status[c].color, status[meetingPlace].color), count |-> status[meetingPlace].count + 1]]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \E c \in Creatures : EnterEmpty(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet ==
  totalMeetings = M => (2 * totalMeetings = status[1].count + status[2].count + status[3].count)

====