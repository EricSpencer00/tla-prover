---- MODULE Chameneos ----
EXTENDS Integers, Sequences

(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN f[x] + Sum(f, S \ {x})

(* ---------------------------------------------------------------------- *)
(* Colors and complement operation                                         *)
(* ---------------------------------------------------------------------- *)

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

(* ---------------------------------------------------------------------- *)
(* Constants                                                               *)
(* ---------------------------------------------------------------------- *)

CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

(* ---------------------------------------------------------------------- *)
(* Variables                                                               *)
(* ---------------------------------------------------------------------- *)

VARIABLES chameneoses, meetingPlace, numMeetings

(* The tuple of variables used for stuttering *)
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

(* ---------------------------------------------------------------------- *)
(* Type invariant                                                          *)
(* ---------------------------------------------------------------------- *)

TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0 .. N

(* ---------------------------------------------------------------------- *)
(* Initial state                                                          *)
(* ---------------------------------------------------------------------- *)

Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0
    /\ TypeOK

(* ---------------------------------------------------------------------- *)
(* Meet action                                                             *)
(* ---------------------------------------------------------------------- *)

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
        /\ numMeetings' = numMeetings + 1
        /\ chameneoses' =
            LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
            IN [chameneoses EXCEPT
                    ![cid] = <<newColor, @[2] + 1>>,
                    ![meetingPlace] = <<newColor, @[2] + 1>>]

(* ---------------------------------------------------------------------- *)
(* Next action (choose a non‑faded creature to try to meet)                *)
(* ---------------------------------------------------------------------- *)

Next ==
    /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
    /\ TypeOK

(* ---------------------------------------------------------------------- *)
(* Specification                                                          *)
(* ---------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars

(* ---------------------------------------------------------------------- *)
(* Safety property (the theorem that TLC is asked to check)               *)
(* ---------------------------------------------------------------------- *)

SumMet == 
    /\ numMeetings = N
    /\ LET f[c \in ChameneosID] == chameneoses[c][2]
       IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====