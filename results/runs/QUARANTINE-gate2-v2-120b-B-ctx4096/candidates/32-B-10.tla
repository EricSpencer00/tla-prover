---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition of a sum over a finite set of identifiers.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors used by the chameneoses.
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

\* Complement of two different colors, otherwise the color stays unchanged.
\* ----------------------------------------------------------------------
Complement(c1, c2) == 
    IF c1 = c2 THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N – total number of meetings after which all chameneoses fade,
\*            M – number of chameneoses.
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

\* Tuple of all variables, used by the temporal operator.
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type invariant.
\* ----------------------------------------------------------------------
TypeOK ==
    /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0 .. N

\* ----------------------------------------------------------------------
\* Initial state: all chameneoses start blue with 0 meetings, the mall is empty.
\* ----------------------------------------------------------------------
Init ==
    /\ chameneoses \in [ ChameneosID -> Color \X {0} ]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* Action for a single chameneos (identified by cid) trying to meet.
\* ----------------------------------------------------------------------
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty THEN
        /\ numMeetings < N
        /\ meetingPlace' = cid
        /\ UNCHANGED <<chameneoses, numMeetings>>
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

\* ----------------------------------------------------------------------
\* When the limit N is reached, any non‑faded chameneos that enters the
\* empty meeting place immediately fades and does not affect other state
\* components.
\* ----------------------------------------------------------------------
FadeIfFull(cid) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings >= N
    /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
    /\ UNCHANGED <<meetingPlace, numMeetings>>

\* ----------------------------------------------------------------------
\* The overall Next action: either a non‑faded chameneos tries to meet,
\* or, after N meetings, it may simply fade.
\* ----------------------------------------------------------------------
Next ==
    \/ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)
    \/ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : FadeIfFull(c)

\* ----------------------------------------------------------------------
\* Full specification.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety property: when numMeetings = N, the sum of individual meeting
\* counters equals 2 * N.
\* ----------------------------------------------------------------------
SumMet ==
    numMeetings = N =>
        LET f[c \in ChameneosesID] == chameneoses[c][2]
        IN Sum(f, ChameneosID) = 2 * N

\* ----------------------------------------------------------------------
\* Theorem stating that the safety property holds throughout every behavior.
\* ----------------------------------------------------------------------
THEOREM Spec => []SumMet

====