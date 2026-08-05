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

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

Init == /\ chameneoses \in [ChameneosesID -> Color \X {0}]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ numMeetings = 0

\* A chameneoses enters an empty meeting place; if all meetings already
\* occurred it takes on the faded color instead.
Meet(cid) == IF meetingPlace = MeetingPlaceEmpty
             THEN IF numMeetings < N
                  THEN meetingPlace' = cid
                       /\ UNCHANGED <<chameneoses, numMeetings>>
                  ELSE chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                       /\ UNCHANGED <<meetingPlace, numMeetings>>
             \* Two chameneoses at a non-empty meeting place meet and mutate.
             ELSE /\ meetingPlace /= cid
                  /\ meetingPlace' = MeetingPlaceEmpty
                  /\ LET newColor == Complement(chameneoses[cid][1],
                                          chameneoses[meetingPlace][1])
                     IN chameneoses' =
                          [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                              ![meetingPlace] = <<newColor, @[2] + 1>>]
                  /\ numMeetings' = numMeetings + 1

Next == /\ meetingPlace' \in ChameneosesID \cup {MeetingPlaceEmpty}
        /\ numMeetings' \in 0 .. N
        /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] /= Faded} : Meet(c)

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of meetings each chameneoses has attended is
\* exactly twice the number of meetings that occurred (each attended twice).
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet

====