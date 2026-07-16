----------------------------- MODULE Chameneos -----------------------------
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

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in Nat

Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* A single chameneos tries to enter the meeting place.
\* If the place is empty and we have not yet reached N meetings, it
\* simply occupies the place.
\* If the place is empty but we already have N meetings, the chameneos
\* fades and the state otherwise stays unchanged.
\* If the place is occupied by another chameneos, the two meet, both
\* update their colors and meeting counters, the place becomes empty,
\* and the global meeting counter is incremented.
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty THEN
      IF numMeetings < N THEN
         /\ meetingPlace' = cid
         /\ UNCHANGED <<chameneoses, numMeetings>>
      ELSE
         /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
         /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE
      /\ meetingPlace /= cid
      /\ meetingPlace' = MeetingPlaceEmpty
      /\ chameneoses' =
            LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
            IN  [chameneoses EXCEPT
                  ![cid]          = <<newColor, @[2] + 1>>,
                  ![meetingPlace] = <<newColor, @[2] + 1>>]
      /\ numMeetings' = numMeetings + 1

\* The system repeatedly lets any non‑faded chameneos attempt to meet.
Next == \E c \in { x \in ChameneosID : chameneoses[x][1] /= Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Upon termination, the sum of the (individual) meetings that all creates have
\* been in, is equal to 2*N.  It is *not* guaranteed that all chameneoses have
\* been in a meeting with another chameneoses.  See section A. Game termination
\* on page 5 of the original paper).
SumMet == numMeetings = N =>
            LET f[c \in ChameneosID] == chameneoses[c][2]
            IN  Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

=============================================================================