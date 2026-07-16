---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

(* --------------------------------------------------------------------- *)
(* Recursive sum over a finite set                                      *)
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

(* --------------------------------------------------------------------- *)
(* Colors and the special faded color                                    *)
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == 
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

(* --------------------------------------------------------------------- *)
(* Constants                                                            *)
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

(* --------------------------------------------------------------------- *)
(* Variables                                                            *)
VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

(* --------------------------------------------------------------------- *)
(* Type invariant                                                       *)
TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

(* --------------------------------------------------------------------- *)
(* Initial predicate                                                    *)
Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0
   /\ TypeOK

(* --------------------------------------------------------------------- *)
(* One possible meeting step                                            *)
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
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN  /\ chameneoses' =
                   [chameneoses EXCEPT
                     ![cid] = <<newColor, @[2] + 1>>,
                     ![meetingPlace] = <<newColor, @[2] + 1>>]
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ numMeetings' = numMeetings + 1
    /\ TypeOK

(* --------------------------------------------------------------------- *)
(* Global next-state action                                              *)
Next ==
    /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)
    /\ UNCHANGED meetingPlace
    \/ UNCHANGED chameneoses
    \/ UNCHANGED numMeetings

(* --------------------------------------------------------------------- *)
(* Full behavior specification                                           *)
Spec == Init /\ [][Next]_vars

(* --------------------------------------------------------------------- *)
(* Termination condition: all chameneoses faded                         *)
AllFaded == \A c \in ChameneosesID : chameneoses[c][1] = Faded

(* --------------------------------------------------------------------- *)
(* Property: upon termination the total number of individual meetings   *)
(* equals 2 * N                                                          *)
SumMet ==
    AllFaded =>
        LET f[c \in ChameneosesID] == chameneoses[c][2]
        IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====