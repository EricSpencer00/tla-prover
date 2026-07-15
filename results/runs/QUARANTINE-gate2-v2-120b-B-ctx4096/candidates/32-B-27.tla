---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)

EXTENDS Integers

(* ---------------------------------------------------------------------- *)
(* Recursive definition of a generic sum over a finite set                  *)
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

(* ---------------------------------------------------------------------- *)
(* Colors and the "faded" sentinel value                                    *)
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

(* Complement of two different colors *)
Complement(c1, c2) == 
    IF c1 = c2 
    THEN c1 
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

(* ---------------------------------------------------------------------- *)
(* Constants: N = number of meetings after which chameneoses fade,
   M = number of chameneoses                                                *)
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

(* ---------------------------------------------------------------------- *)
(* Variables *)
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M

(* A distinguished value meaning "no one is waiting in the meeting place" *)
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

(* ---------------------------------------------------------------------- *)
(* Type correctness invariant *)
TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0 .. N

(* ---------------------------------------------------------------------- *)
(* Initial state *)
Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

(* ---------------------------------------------------------------------- *)
(* The action of a chameneos with identifier cid trying to meet *)
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
            /\ meetingPlace' = cid
            /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE
            /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
            /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE
        /\ meetingPlace # cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN chameneoses' =
                [chameneoses EXCEPT 
                    ![cid] = <<newColor, @[2] + 1>>,
                    ![meetingPlace] = <<newColor, @[2] + 1>>]
        /\ numMeetings' = numMeetings + 1

(* ---------------------------------------------------------------------- *)
(* Next-state relation: any non‑faded chameneos may try to meet *)
Next ==
    \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)

(* ---------------------------------------------------------------------- *)
(* Full specification *)
Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Desired invariant: when the required number of meetings has occurred,
   the total count of individual meetings equals 2*N. *)
SumMet ==
    numMeetings = N
    => LET f[c \in ChameneosesID] == chameneoses[c][2]
       IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====