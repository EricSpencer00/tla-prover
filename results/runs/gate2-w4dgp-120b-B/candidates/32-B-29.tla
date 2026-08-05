---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent and          *)
(* symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf       *)
(***************************************************************************)
EXTENDS Integers

RecurS(f, S) == IF S = {} THEN 0
                ELSE LET x == CHOOSE x \in S : TRUE
                     IN  f[x] + RecurS(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* N - total number of meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}

Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

Meet(cid) ==
    /\ meetingPlace' = IF meetingPlace = MeetingPlaceEmpty
                         THEN IF numMeetings < N THEN cid ELSE meetingPlace
                         ELSE MeetingPlaceEmpty
    /\ chameneoses' = IF meetingPlace = MeetingPlaceEmpty
                         THEN IF numMeetings < N
                                 THEN chameneoses
                                 ELSE [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                         ELSE LET newColor == Complement(chameneoses[cid][1],
                                                         chameneoses[meetingPlace][1])
                              IN [chameneoses EXCEPT
                                    ![cid] = <<newColor, @[2] + 1>>,
                                    ![meetingPlace] = <<newColor, @[2] + 1>>]
    /\ numMeetings' = IF meetingPlace # MeetingPlaceEmpty /\ meetingPlace # cid
                         THEN numMeetings + 1
                         ELSE numMeetings

Next == \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
Spec == Init /\ [][Next]_vars

\* Upon termination, twice the number of meetings equals the sum of the
\* individual meetings each chameneoses has been in.  Not every chameneoses
\* necessarily meets another, see section A. Game termination of the paper.
SumMet == numMeetings = N => LET f[c \in ChameneosID] == chameneoses[c][2]
                             IN RecurS(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet
====