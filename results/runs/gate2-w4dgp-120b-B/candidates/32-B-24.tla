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

\* N - number of total meetings after which chameneoses fade
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

Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

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

\* Repeatedly try to enter the meeting place for chameneoses that are not
\* faded yet.  The system terminates once the color of all chameneoses is faded.
Next == /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] /= Faded} : Meet(c)
        /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the meetings that all chameneoses have been
\* in is exactly 2*N.  It is *not* guaranteed that all chameneoses have been in
\* a meeting (cf. Game termination on page 5 of the paper).
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet
====