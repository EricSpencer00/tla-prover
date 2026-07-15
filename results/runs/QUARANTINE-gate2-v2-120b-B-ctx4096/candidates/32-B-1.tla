---- MODULE Chameneos ----
EXTENDS Integers

(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN f[x] + Sum(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* Initial state: every chameneos starts with a colour and zero meetings.
Init ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0
    /\ chameneoses = [i \in ChameneosesID |-> <<CHOOSE c \in Color : TRUE, 0>>]

\* A chameneos attempts to enter the meeting place.
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
            /\ meetingPlace' = cid
            /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE
            /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
            /\ meetingPlace' = MeetingPlaceEmpty
            /\ UNCHANGED numMeetings
    ELSE
        /\ meetingPlace /= cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ numMeetings' = numMeetings + 1
        /\ chameneoses' =
            LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
            IN [chameneoses EXCEPT
                    ![cid]          = <<newColor, chameneoses[cid][2] + 1>>,
                    ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]

\* Repeatedly pick a non‑faded chameneos to act.
Next ==
    /\ \E c \in { i \in ChameneosID : chameneoses[i][1] # Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the individual meeting counters equals 2*N.
SumMet ==
    /\ numMeetings = N
    /\ LET f[c \in ChameneosID] == chameneoses[c][2]
       IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====