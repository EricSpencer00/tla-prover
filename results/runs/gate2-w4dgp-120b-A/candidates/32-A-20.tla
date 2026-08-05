---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

VARIABLES chmn, meetingPlace, totalMeetings
vars == <<chmn, meetingPlace, totalMeetings>>

Colors == {"blue", "red", "yellow", Faded}

\* Fresh(color1, color2): the complement rule for two meeting creatures.
Fresh(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE (CHOOSE c \in Colors \ {c1, c2} : TRUE)

\* Sum of meetings each creature has participated in.
SumMet == LET f[S \in SUBSET (1..N)] ==
              IF S = {} THEN 0
              ELSE LET x == CHOOSE y \in S : TRUE IN chmn[x][2] + f[S \ {x}]
          IN f[1..N]

TypeOK ==
  /\ chmn \in [1..N -> [1..2]]
  /\ \A k \in 1..N : chmn[k][1] \in Colors
  /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ chmn = [k \in 1..N |-> <<CHOOSE cl \in {"blue", "red", "yellow"} : TRUE, 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* An arriving creature finds the meeting place empty and waits.
EnterPlace(k) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ chmn[k][1] # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = k
  /\ UNCHANGED <<chmn, totalMeetings>>

\* With the meeting place closed, a creature that tries to enter fades out.
FadeOut(k) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = M
  /\ chmn[k][1] # Faded
  /\ chmn' = [chmn EXCEPT ![k] = <<Faded, chmn[k][2]>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Two different creatures meet and both change to the complement color.
Meet(k) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # k
  /\ LET newCol == Fresh(chmn[meetingPlace][1], chmn[k][1]) IN
       chmn' = [chmn EXCEPT ![meetingPlace] = <<newCol, chmn[meetingPlace][2] + 1>,
                               ![k] = <<newCol, chmn[k][2] + 1>>]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E k \in 1..N : EnterPlace(k) \/ FadeOut(k) \/ Meet(k)

Spec == Init /\ [][Next]_vars

\* When the meeting place has closed, every reported meeting is accounted for
\* twice, once against each participant of that meeting.
MeetingCountMatches == totalMeetings = M => SumMet = 2 * M

====