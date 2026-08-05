---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

N \in Nat \ {0}
M \in Nat \ {0}
ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

vars == <<chameneoses, meetingPlace, numMeetings>>

\* For each chameneoses, remember its current color and how many meetings it
\* has been in.
TypeOK ==
  /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
  /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

\* The number of meetings after which chameneoses no longer enter meetings.
N == 4

Init ==
  /\ chameneoses \in [ ChameneosesID -> Color \X {0} ]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* chameneoses takes the empty meeting place or enters a meeting with the
\* creature that is already waiting.
Meet(c) ==
  /\ meetingPlace' = IF meetingPlace = MeetingPlaceEmpty THEN c
                      ELSE IF meetingPlace = c THEN meetingPlace
                           ELSE MeetingPlaceEmpty
  /\ chameneoses' = IF meetingPlace = MeetingPlaceEmpty
                    THEN chameneoses
                    ELSE IF meetingPlace = c
                         THEN chameneoses
                         ELSE LET newColor == Complement(chameneoses[c][1],
                                                        chameneoses[meetingPlace][1])
                              IN [chameneoses EXCEPT ![c] = <<newColor, @[2] + 1>>,
                                                   ![meetingPlace] = <<newColor, @[2] + 1>>]
  /\ numMeetings' = IF meetingPlace = MeetingPlaceEmpty \/ meetingPlace = c
                     THEN numMeetings
                     ELSE numMeetings + 1

\* Repeatedly try to enter the meeting place. The system terminates once all
\* chameneoses have faded.
Next == \E c \in ChameneosesID : Meet(c)

Spec == Init /\ [][Next]_vars

\* Once the meeting place is empty, the sum of each chameneos' individual
\* meeting-counts is exactly 2 * the number of meetings that took place.
SumMet == meetingPlace = MeetingPlaceEmpty => LET f[c \in ChameneosesID] == chameneoses[c][2]
                                             IN Sum(f, ChameneosesID) = 2 * numMeetings

=============================================================================