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

\* N - number of total meeting after which chameneoses fade
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

Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* The meeting place (called the Mall in the original paper) keeps track of
\* which chameneoses creature is currently waiting to meet another
\* creature: a meeting takes place when two non-faded chameneoses are at the
\* meeting place at the same time, and the two chameneoses split their
\* meeting count and update their colors.  Once the number of meetings hits
\* N, the meeting place simply refuses new entries and keeps the chameneoses
\* that are left waiting there, so nothing is lost.
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty
   THEN IF numMeetings < N
        THEN /\ meetingPlace' = cid
             /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
             /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE /\ meetingPlace # cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ numMeetings' = numMeetings + 1
        /\ chameneoses' =
             LET newColor == Complement(chameneoses[cid][1],
                                        chameneoses[meetingPlace][1])
             IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                         ![meetingPlace] = <<newColor, @[2] + 1>>]

Next ==
   /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)
   /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Upon termination (all chameneoses faded), the sum of the individual
\* meeting counts that each chameneoses has been in is equal to 2*N.
\* It is *not* guaranteed that all chameneoses have been in a meeting with
\* another chameneoses; see section A. Game termination, page 5 of the
\* original paper.
SumMet ==
   numMeetings = N =>
      LET f[c \in ChameneosesID] == chameneoses[c][2]
      IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet

====