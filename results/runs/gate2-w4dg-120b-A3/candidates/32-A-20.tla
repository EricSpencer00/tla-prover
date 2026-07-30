---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature is a pair: its color and the number of meetings it participated in.
Creatures == [1..N -> {Faded, "blue", "red", "yellow"} \X (0..M)]

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOver(f, S \ {x})

\* Individual meetings counted per creature vs. twice the global count.
IndividualMeetings == SumOver([c \in 1..N |-> Creatures[c][2]], 1..N)

Complement(c, d) ==
  IF c = d THEN c
  ELSE IF (c = "blue" /\ d = "red") \/ (c = "red" /\ d = "blue") THEN "yellow"
  ELSE IF (c = "blue" /\ d = "yellow") \/ (c = "yellow" /\ d = "blue") THEN "red"
  ELSE IF (c = "red" /\ d = "yellow") \/ (c = "yellow" /\ d = "red") THEN "blue"
  ELSE Faded

VARIABLES creatures, meetingPlace, totalMeetings

vars == <<creatures, meetingPlace, totalMeetings>>

Init ==
  /\ \E initColors \in [1..N -> {"blue", "red", "yellow"}] :
       creatures = [c \in 1..N |-> <<initColors[c], 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* A creature enters the meeting place when it is empty and the session is open.
Enter(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ creatures[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<creatures, totalMeetings>>

\* With the session closed a creature trying to join fades instead.
Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ creatures[c][1] # Faded
  /\ creatures' = [creatures EXCEPT ![c] = <<Faded, creatures[c][2]>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Two distinct creatures at the place both adopt their complement and leave.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ creatures[c][1] # Faded
  /\ LET other == meetingPlace IN
       /\ creatures' = [creatures EXCEPT
                         ![c] = <<Complement(creatures[c][1], creatures[other][1]),
                                   creatures[c][2] + 1>>,
                         ![other] = <<Complement(creatures[c][1], creatures[other][1]),
                                      creatures[other][2] + 1>>]
       /\ totalMeetings' = totalMeetings + 1
       /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \E c \in 1..N :
    \/ Enter(c)
    \/ Fade(c)
    \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Colors and meeting-place occupants stay inside their declared ranges.
TypeOK ==
  /\ creatures \in Creatures
  /\ meetingPlace \in {MeetingPlaceEmpty} \cup (1..N)
  /\ totalMeetings \in 0..M

\* Global meetings account for exactly half the per-creature meeting count.
SumMet == totalMeetings = M => IndividualMeetings = 2 * M

====