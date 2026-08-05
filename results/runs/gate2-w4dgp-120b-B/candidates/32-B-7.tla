---- MODULE Chameneos ----
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

\* N - number of total meeting after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* A chameneoses enters the meeting place to wait for a partner.
\* Once the meeting place is full a meeting takes place.
\* A chameneoses that enters the meeting place after the game limit has
\* been reached simply fades away.
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty
   THEN IF numMeetings < N
        THEN /\ meetingPlace' = cid
             /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
             /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE IF meetingPlace /= cid
        THEN /\ meetingPlace' = MeetingPlaceEmpty
             /\ chameneoses' =
                  LET newColor == Complement(chameneoses[cid][1],
                                            chameneoses[meetingPlace][1])
                  IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                          ![meetingPlace] = <<newColor, @[2] + 1>>]
             /\ numMeetings' = numMeetings + 1
        ELSE /\ meetingPlace' = meetingPlace
             /\ chameneoses' = chameneoses
             /\ numMeetings' = numMeetings

\* Any chameneoses that has not faded yet may repeatedly try to enter
\* the meeting place.
Next == \/ \E c \in { x \in ChameneosesID : chameneoses[x][1] /= Faded} : Meet(c)
        \/ /\ meetingPlace' = meetingPlace
           /\ chameneoses' = chameneoses
           /\ numMeetings' = numMeetings

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the (individual) meetings that all creates
\* have been in, is exactly 2*N.  (A terminalising run can in principle
\* leave some chameneoses untouched.)
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet
====