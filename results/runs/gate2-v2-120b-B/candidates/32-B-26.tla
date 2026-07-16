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

\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

(* The original specification used a subtle combination of \/ and UNCHANGED
   that left some variables undefined in certain branches.  The following
   rewritten definition of Meet preserves the intended behaviour while
   guaranteeing that every variable is assigned a value in every branch. *)
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
           /\ meetingPlace' = cid
           /\ chameneoses' = chameneoses
           /\ numMeetings' = numMeetings
        ELSE
           /\ meetingPlace' = meetingPlace
           /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
           /\ numMeetings' = numMeetings
   ELSE
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ chameneoses' =
              LET newColor == Complement(chameneoses[cid][1],
                                         chameneoses[meetingPlace][1])
              IN  [chameneoses EXCEPT
                     ![cid]            = <<newColor, chameneoses[cid][2] + 1>>,
                     ![meetingPlace]   = <<newColor, chameneoses[meetingPlace][2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* Repeatedly try to enter meeting place for chameneoses that are not faded yet.
\* The system terminates once the color of all chameneoses is faded.
Next ==
   /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Upon termination, the sum of the (individual) meetings that all creatures have
\* been in, is equal to 2*N.  It is *not* guaranteed that all chameneoses have
\* been in a meeting with another chameneoses.  See section A. Game termination
\* on page 5 of the original paper.
SumMet == numMeetings = N =>
            LET f[c \in ChameneosID] == chameneoses[c][2]
            IN  Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====