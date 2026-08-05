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

-----------------------------------------------------------------------------

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

-----------------------------------------------------------------------------

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

Init == /\ chameneoses \in [ChameneosesID -> Color \X {0}]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ numMeetings = 0

\* When no chameneoses is waiting to meet, a non-faded one enters the
\* meeting place.  If the meeting-place is already occupied, the two
\* chameneoses at it mutate their color and the meeting counter.
\* When the meeting budget N is spent, the waiting chameneoses takes on
\* a faded color and effectively leaves the game.
Meet(cid) == IF meetingPlace = MeetingPlaceEmpty
             THEN IF numMeetings < N
                       THEN /\ meetingPlace' = cid
                            /\ UNCHANGED <<chameneoses, numMeetings>>
                       ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                            /\ UNCHANGED <<meetingPlace, numMeetings>>
             ELSE /\ meetingPlace /= cid
                  /\ meetingPlace' = MeetingPlaceEmpty
                  /\ chameneoses' =
                        LET newColor == Complement(chameneoses[cid][1],
                                                  chameneoses[meetingPlace][1])
                        IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                               ![meetingPlace] = <<newColor, @[2] + 1>>]
                  /\ numMeetings' = numMeetings + 1

\* Repeatedly try to enter the meeting place, for chameneoses that are not
\* faded yet.  The system terminates once all chameneoses are faded.
Next == /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] /= Faded} : Meet(c)

Spec == Init /\ [][Next]_vars

SpecTypeOK == Spec /\ TypeOK

\* At termination the sum of individual meetings equals exactly 2*N.
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM SpecTypeOK => []SumMet

=============================================================================