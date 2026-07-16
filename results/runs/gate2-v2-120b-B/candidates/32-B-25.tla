---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive sum operator over a finite set
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
            ELSE LET x == CHOOSE x \in S : TRUE
                 IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and complementary operation
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constant parameters
\* ----------------------------------------------------------------------
\* N – total number of meetings after which chameneoses fade
\* M – number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type invariant (helps readability, not used for safety)
\* ----------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* Meet action – the only possible transition
\* ----------------------------------------------------------------------
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
            /\ meetingPlace' = cid
            /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE
            /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @@[cid][2]>>]
            /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE
        /\ meetingPlace /= cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN  chameneoses' =
               [chameneoses EXCEPT
                    ![cid] = <<newColor, chameneoses[cid][2] + 1>>,
                    ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation: any non‑faded chameneos may try to meet
\* ----------------------------------------------------------------------
Next ==
    /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Desired property: when numMeetings reaches N, the total count of
\* individual meetings equals 2 * N
\* ----------------------------------------------------------------------
SumMet ==
    numMeetings = N =>
        LET f[c \in ChameneosID] == chameneoses[c][2]
        IN  Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====