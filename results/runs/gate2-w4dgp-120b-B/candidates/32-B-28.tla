---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent and      *)
(* symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf      *)
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

Init == /\ chameneoses \in [ChameneosesID -> Color \X {0}]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ numMeetings = 0

\* Any chameneoses that is not faded yet is allowed to enter the meeting
\* place (called the Mall in the original paper).  When a meeting place is
\* already occupied, the meeting takes place and both participants adopt the
\* complementary color.
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty
      THEN IF numMeetings < N
              THEN /\ meetingPlace' = cid
                   /\ UNCHANGED <<chameneoses, numMeetings>>
              ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                   /\ UNCHANGED <<meetingPlace, numMeetings>>
      ELSE /\ meetingPlace # cid
           /\ meetingPlace' = MeetingPlaceEmpty
           /\ chameneoses' =
                 LET newColor == Complement(chameneoses[cid][1],
                                            chameneoses[meetingPlace][1])
                 IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                           ![meetingPlace] = <<newColor, @[2] + 1>>]
           /\ numMeetings' = numMeetings + 1

Next == /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)
        /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the meetings that each chameneoses has been
\* in is two times the total number of meetings (a meeting involves both
\* participants).  It is NOT guaranteed that every chameneoses has actually
\* been in a meeting.
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet

====