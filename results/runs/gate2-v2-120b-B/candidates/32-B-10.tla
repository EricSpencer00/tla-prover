---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ------------------------------------------------------------------------
\* Recursive definition of a finite sum over a set.
\* ------------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

\* ------------------------------------------------------------------------
\* Basic constants.
\* ------------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == 
    IF c1 = c2 
    THEN c1 
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ------------------------------------------------------------------------
\* Configuration constants.
\* N – total number of meetings after which chameneoses fade.
\* M – number of chameneoses.
\* ------------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in Nat \ {0}
ASSUME M \in Nat \ {0}

VARIABLES chameneoses, meetingPlace, numMeetings

\* Group the variables for stuttering.
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ------------------------------------------------------------------------
\* Type invariant.
\* ------------------------------------------------------------------------
TypeOK ==
    /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in Nat

\* ------------------------------------------------------------------------
\* Initial predicate.
\* Each chameneos starts with a non‑faded color and zero meetings.
\* ------------------------------------------------------------------------
Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

\* ------------------------------------------------------------------------
\* Single meeting step for chameneos identifier cid.
\* The step is fully specified for all variables.
\* ------------------------------------------------------------------------
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
        /\ numMeetings' = numMeetings + 1
        /\ chameneoses' =
            LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
            IN [chameneoses EXCEPT
                    ![cid]          = <<newColor, @[2] + 1>>,
                    ![meetingPlace] = <<newColor, @[2] + 1>>]

\* ------------------------------------------------------------------------
\* The system repeatedly lets any non‑faded chameneos attempt to meet.
\* ------------------------------------------------------------------------
Next ==
    \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)

\* ------------------------------------------------------------------------
\* Full specification.
\* ------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ------------------------------------------------------------------------
\* Safety property: when numMeetings = N, the total number of individual
\* meetings equals 2*N.
\* ------------------------------------------------------------------------
SumMet ==
    numMeetings = N =>
        LET f == [c \in ChameneosID |-> chameneoses[c][2]]
        IN Sum(f, ChameneosID) = 2 * N

\* ------------------------------------------------------------------------
\* The theorem that TLC will check.
\* ------------------------------------------------------------------------
THEOREM Spec => []SumMet

====