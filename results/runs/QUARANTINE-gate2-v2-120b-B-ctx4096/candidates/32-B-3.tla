---- MODULE Chameneos ----
EXTENDS Integers

(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)

(* ---------------------------------------------------------------------- *)
(* Recursive sum over a finite set                                         *)
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

(* ---------------------------------------------------------------------- *)
(* Colors and faded color                                                  *)
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

(* Complement returns the third color when the two arguments differ *)
Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

(* ---------------------------------------------------------------------- *)
(* Constants                                                               *)
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

(* ---------------------------------------------------------------------- *)
(* State variables                                                         *)
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M

(* Choose a distinguished value that is not a chameneos identifier. *)
MeetingPlaceEmpty == CHOOSE e \in {0} : e \notin ChameneosID

(* Type invariant                                                          *)
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in Nat

(* ---------------------------------------------------------------------- *)
(* Initial state                                                           *)
Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

(* ---------------------------------------------------------------------- *)
(* Action for a single chameneos                                            *)
(* cid is the identifier of the chameneos that is trying to act.           *)
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
         IN [chameneoses EXCEPT
                ![cid] = <<newColor, @[2] + 1>>,
                ![meetingPlace] = <<newColor, @[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

(* ---------------------------------------------------------------------- *)
(* Choose a non‑faded chameneos to act                                      *)
Next ==
  /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)
  /\ UNCHANGED <<>>

(* ---------------------------------------------------------------------- *)
(* Full specification                                                       *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Safety property: sum of individual meeting counts equals 2*N when the   *)
(* total number of meetings has reached N.                                   *)
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosesID] == chameneoses[c][2]
    IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====