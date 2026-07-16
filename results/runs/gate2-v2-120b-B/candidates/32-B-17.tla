---- MODULE Chameneos ----
(* Fixed version of the Chameneos specification: ensures that every next-state
   action assigns a value to each variable (meetingPlace and numMeetings) while
   preserving the original semantics. *)

EXTENDS Integers

(* ------------------------------------------------------------------------- *)
(* Recursive sum over a finite set, unchanged from the original specification. *)
(* ------------------------------------------------------------------------- *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* ------------------------------------------------------------------------- *)
(* Colours and the function that computes the complementary colour.            *)
(* ------------------------------------------------------------------------- *)
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

(* ------------------------------------------------------------------------- *)
(* Constants: N – total meetings after which chameneoses fade; M – number of *)
(* chameneoses. The original assumptions are retained.                       *)
(* ------------------------------------------------------------------------- *)
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

(* ------------------------------------------------------------------------- *)
(* Type invariant (unchanged).                                               *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
  /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}

(* ------------------------------------------------------------------------- *)
(* Initial state (unchanged).                                                *)
(* ------------------------------------------------------------------------- *)
Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

(* ------------------------------------------------------------------------- *)
(* Meet action – rewritten so that every branch assigns a value to every   *)
(* variable. The logical behaviour is identical to the original version.    *)
(* ------------------------------------------------------------------------- *)
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ numMeetings' = N               \* keep N unchanged
      /\ meetingPlace' = MeetingPlaceEmpty
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
  ELSE
    /\ meetingPlace /= cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ numMeetings' = numMeetings + 1
    /\ chameneoses' =
        LET newColor == Complement(chameneoses[cid][1],
                                   chameneoses[meetingPlace][1])
        IN [chameneoses EXCEPT
              ![cid] = <<newColor, @[2] + 1>>,
              ![meetingPlace] = <<newColor, @[2] + 1>>]

(* ------------------------------------------------------------------------- *)
(* Next action – unchanged except that it now uses the corrected Meet.      *)
(* ------------------------------------------------------------------------- *)
Next ==
  /\ \E c \in { x \in ChameneosID : chameneoses[x][1] /= Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Safety property: when numMeetings = N, the total number of individual   *)
(* meetings equals 2*N.                                                       *)
(* ------------------------------------------------------------------------- *)
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====