---- MODULE Chameneos ----
EXTENDS Integers, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are identified by the numbers 1..N. Each maps to a pair
\* consisting of its current color and its individual meeting count.
Creatures == 1..N

Colors == {"blue", "red", "yellow"}

VARIABLES colCount, meetingPlace, totalMeetings

vars == <<colCount, meetingPlace, totalMeetings>>

TypeOK ==
  /\ colCount \in [Creatures -> (Colors \cup {Faded}) \X (0..M)]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

RECURSIVE SumUp(_)
SumUp(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN colCount[c][2] + SumUp(S \ {c})

RECURSIVE Tally(_)
Tally(S) ==
  IF S = {} THEN 0
  ELSE LET c == CHOOSE x \in S : TRUE IN colCount[c][2] + Tally(S \ {c})

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET rest == {"blue", "red", "yellow"} \ {c1, c2} IN CHOOSE c \in rest : TRUE

Init ==
  /\ \E initColors \in [Creatures -> Colors] :
       colCount = [c \in Creatures |-> <<initColors[c], 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ colCount[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<colCount, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ colCount[c][1] # Faded
  /\ colCount' = [colCount EXCEPT ![c] = <<Faded, colCount[c][2>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ colCount[c][1] # Faded
  /\ colCount[meetingPlace][1] # Faded
  /\ LET newColor == Complement(colCount[c][1], colCount[meetingPlace][1]) IN
       /\ colCount' = [colCount EXCEPT ![c] = <<newColor, colCount[c][2] + 1>>, ![meetingPlace] = <<newColor, colCount[meetingPlace][2] + 1>>]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalMeetings' = totalMeetings + 1

Next ==
  \E c \in Creatures : EnterMeetingPlace(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* When the meeting place has closed, every creature that still holds a
\* non-faded color must have already participated in at least one meeting.
SumMet == (totalMeetings = M) => (Tally(Creatures) = 2 * totalMeetings)

====