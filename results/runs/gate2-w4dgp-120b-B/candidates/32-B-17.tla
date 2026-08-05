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

(* N - number of total meeting after which chameneoses fade
   M - number of chameneoses *)
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

Init == /\ chameneoses \in [ChameneosesID -> Color \X {0}]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ numMeetings = 0

\* Only a non-faded chameneoses takes a step, and only enter an empty meeting
\* place when there is still room for another meeting.
NextStep(c) == /\ chameneoses[c][1] # Faded
                /\ numMeetings < N
                /\ meetingPlace = MeetingPlaceEmpty
                /\ meetingPlace' = c
                /\ UNCHANGED <<chameneoses, numMeetings>>

\* A chameneoses in the meeting place is faded when no more meetings remain.
Fade(c) == /\ meetingPlace = MeetingPlaceEmpty
            /\ numMeetings >= N
            /\ chameneoses[c][1] # Faded
            /\ chameneoses' = [chameneoses EXCEPT ![c] = <<Faded, @[2]>>]
            /\ UNCHANGED <<meetingPlace, numMeetings>>

\* Two chameneoses in the meeting place mutate each other and leave.
Mutate(c) == /\ meetingPlace # MeetingPlaceEmpty
              /\ meetingPlace # c
              /\ meetingPlace' = MeetingPlaceEmpty
              /\ numMeetings' = numMeetings + 1
              /\ LET newColor == Complement(chameneoses[c][1],
                                            chameneoses[meetingPlace][1])
                 IN chameneoses' =
                      [chameneoses EXCEPT ![c] = <<newColor, @[2] + 1>>,
                                       ![meetingPlace] = <<newColor, @[2] + 1>>]

Next == \E c \in ChameneosesID : NextStep(c) \/ Fade(c) \/ Mutate(c)

Spec == Init /\ [][Next]_vars

(* Upon termination, the sum of the meetings each chameneoses has been in is
   exactly 2*N; it is *not* guaranteed that all chameneoses have been in a meeting
   with another chameneoses. *)
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet

====