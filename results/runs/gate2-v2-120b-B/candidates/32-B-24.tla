---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

(***************************************************************************)
(* Helper definitions                                                     *)
(***************************************************************************)

\* Sum over a finite set S of the values produced by function f
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* Colors used in the game
Color == {"blue", "red", "yellow"}

\* A distinguished value that is not a regular color, used to denote a
\* faded creature.  The exact value is irrelevant as long as it is not in
\* Color.
Faded == CHOOSE c : c \notin Color

\* Complementary color computation, unchanged from the original spec
Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

(***************************************************************************)
(* Constants (as in the original paper)                                   *)
(***************************************************************************)

\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M

\* A special value that is never a valid chameneos identifier, used to
\* represent an empty meeting place.
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

(***************************************************************************)
(* Type correctness invariant (unchanged)                                 *)
(***************************************************************************)

TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)

Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

(***************************************************************************)
(* Meet action – now fully specifies all variables in every branch      *)
(***************************************************************************)

Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
      /\ meetingPlace' = MeetingPlaceEmpty
      /\ numMeetings' = numMeetings
  ELSE
    /\ meetingPlace /= cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ chameneoses' =
         LET newColor == Complement(chameneoses[cid][1],
                                   chameneoses[meetingPlace][1])
         IN [chameneoses EXCEPT
               ![cid] = <<newColor, @[2] + 1>>,
               ![meetingPlace] = <<newColor, @[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

(***************************************************************************)
(* Next-state relation                                                    *)
(***************************************************************************)

Next ==
  \E c \in { x \in ChameneosesID : chameneoses[x][1] /= Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Liveness / safety property (unchanged)                                 *)
(***************************************************************************)

\* Upon termination, the sum of the (individual) meetings that all creatures have
\* been in, is equal to 2*N.  It is *not* guaranteed that all chameneoses have
\* been in a meeting with another chameneoses.
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosesID] == chameneoses[c][2]
    IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====