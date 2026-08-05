---- MODULE Chameneos ----
EXTENDS Integers

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures are numbered 1..N; the meeting place admits at most one waiting creature at a time.
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
Doubles(n) == n * (n + 1)

VARIABLES colCount, meetingPlace, meetingsTotal
vars == <<colCount, meetingPlace, meetingsTotal>>

\* Complement rule: two colors produce the third, while identical colors leave unchanged.
Complement == [x \in Colors, y \in Colors |-> IF x = y THEN x ELSE
                 CHOOSE z \in {"blue", "red", "yellow"} :
                   (z # x) /\ (z # y)]

InitColor(c) == CHOOSE x \in {"blue", "red", "yellow"} : TRUE

TypeOK ==
  /\ colCount \in [Creatures -> Colors \X (1..Doubles(M))]
  /\ meetingPlace \in (Creatures \cup {MeetingPlaceEmpty})
  /\ meetingsTotal \in 0..M

Init ==
  /\ colCount = [c \in Creatures |-> <<InitColor(c), 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal = 0

\* A fresh creature enters the empty meeting place to wait for a partner.
EnterPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal < M
  /\ colCount[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<colCount, meetingsTotal>>

\* The meeting place is closed: a creature that arrives now fades out.
Fade(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ meetingsTotal = M
  /\ colCount[c][1] # Faded
  /\ colCount' = [colCount EXCEPT ![c] = <<Faded, colCount[c][2>>]
  /\ UNCHANGED <<meetingPlace, meetingsTotal>>

\* A meeting happens between the arriving creature and the one waiting in the place; both
\* adopt the complement of their two colors and leave the place empty.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ meetingsTotal < M
  /\ colCount[c][2] < Doubles(M)
  /\ colCount[meetingPlace][2] < Doubles(M)
  /\ LET nm == Complement[colCount[c][1], colCount[meetingPlace][1]] IN
       colCount' = [colCount EXCEPT ![c] = <<nm, colCount[c][2] + 1>>,
                    ![meetingPlace] = <<nm, colCount[meetingPlace][2] + 1>>]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ meetingsTotal' = meetingsTotal + 1

Next == \E c \in Creatures : EnterPlace(c) \/ Fade(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

\* Every meeting is a pairwise event, so when the meeting place has closed the sum of all
\* individual creature meeting counts must be exactly twice the number of meetings that occurred.
SumMet ==
  (meetingsTotal = M) =>
    (2 * meetingsTotal = (colCount[1][2] + colCount[2][2] + colCount[3][2]))

====