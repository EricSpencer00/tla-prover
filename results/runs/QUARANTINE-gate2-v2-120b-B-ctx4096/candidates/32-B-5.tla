---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

(* Recursive sum over a finite set of IDs, using a total function f. *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE x \in S : TRUE
    IN f[x] + Sum(f, S \ {x})

(* Colors and a special "faded" value that is guaranteed not to be a color. *)
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

(* Complementary color when two different colors meet. *)
Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

(* N - number of total meetings after which chameneoses fade
   M - number of chameneoses *)
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M

(* A distinguished value meaning "no one is waiting". *)
MeetingPlaceEmpty == 0

(* Type correctness invariant. *)
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in 0 .. N

(* Initial state: all chameneoses are blue and have attended 0 meetings. *)
Init ==
  /\ chameneoses = [i \in ChameneosID |-> << "blue", 0 >>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

(* One chameneos (cid) attempts to meet. *)
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ meetingPlace' = MeetingPlaceEmpty
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
      /\ UNCHANGED numMeetings
  ELSE
    /\ meetingPlace # cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ chameneoses' =
         LET newColor == Complement(chameneoses[cid][1],
                                    chameneoses[meetingPlace][1])
         IN [chameneoses EXCEPT
               ![cid]         = <<newColor, chameneoses[cid][2] + 1>>,
               ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
    /\ numMeetings' = numMeetings + 1

(* Next action: any non‑faded chameneos may try to meet. *)
Next ==
  \E c \in { i \in ChameneosID : chameneoses[i][1] # Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

(* Desired safety property: when the prescribed number of meetings has been
   reached, the total number of individual meetings equals twice that number. *)
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====