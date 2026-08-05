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

\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* chameneoses enters empty meeting place or, when meetings are exhausted,
\* takes the faded color and becomes unavailable for further meetings.
Meet(cid) ==
   /\ meetingPlace' = IF meetingPlace = MeetingPlaceEmpty /\ numMeetings < N
                      THEN cid
                      ELSE IF meetingPlace = MeetingPlaceEmpty /\ numMeetings >= N
                           THEN MeetingPlaceEmpty
                           ELSE MeetingPlaceEmpty
   /\ chameneoses' = IF meetingPlace = MeetingPlaceEmpty /\ numMeetings >= N
                     THEN [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
                     ELSE IF meetingPlace # MeetingPlaceEmpty /\ meetingPlace # cid
                          THEN LET newColor == Complement(chameneoses[cid][1],
                                                          chameneoses[meetingPlace][1])
                               IN [chameneoses EXCEPT ![cid] = <<newColor, chameneoses[cid][2] + 1>>,
                                                        ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
                          ELSE chameneoses
   /\ numMeetings' = IF meetingPlace # MeetingPlaceEmpty /\ meetingPlace # cid
                     THEN numMeetings + 1
                     ELSE numMeetings

\* Repeatedly try to enter meeting place for chameneoses that are not faded.
\* The system terminates once the color of all chameneoses is faded.
Next == \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the individual meetings that all chameneoses
\* have been in is equal to 2*N.
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
====