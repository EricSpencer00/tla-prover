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

(* N - number of total meetings after which chameneoses fade
   M - number of chameneoses *)
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* chameneoses enters an empty meeting place; once the game is exhausted it
\* takes on a 'faded' color and is never allowed to re-enter.
EnterMeetingPlace(cid) ==
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings < N
   /\ meetingPlace' = cid
   /\ UNCHANGED <<chameneoses, numMeetings>>

\* The meeting place is not empty: two chameneoses mutate and the place clears.
Mutate(cid) ==
   /\ meetingPlace # MeetingPlaceEmpty
   /\ meetingPlace # cid
   /\ meetingPlace' = MeetingPlaceEmpty
   /\ chameneoses' =
        LET newColor == Complement(chameneoses[cid][1], chameneoses[meetingPlace][1])
        IN  [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>, ![meetingPlace] = <<newColor, @[2] + 1>>]
   /\ numMeetings' = numMeetings + 1

\* A chameneoses that is already faded no longer participates.
Next ==
   \/ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : EnterMeetingPlace(c)
   \/ \E c \in ChameneosesID : Mutate(c)

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the meetings all chameneoses have been in is
\* twice the number of meetings run - each meeting counts for its two participants.
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet

====