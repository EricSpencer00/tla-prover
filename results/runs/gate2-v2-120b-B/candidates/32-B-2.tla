---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)

EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive Sum operator
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors, faded color, and complement operation
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == 
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N = total number of meetings, M = number of chameneoses
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type OK invariant (kept for readability, not used in the safety proof)
\* ----------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
   /\ chameneoses = [i \in ChameneosesID |-> <<Color[1], 0>>]   \* all start "blue", 0 meetings
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* Meet action – now fully specifies all variables in every branch
\* ----------------------------------------------------------------------
Meet(cid) == 
    IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
            /\ meetingPlace' = cid
            /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE
            /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
            /\ meetingPlace' = MeetingPlaceEmpty
            /\ numMeetings' = numMeetings
    ELSE
        /\ meetingPlace /= cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN chameneoses' =
                [chameneoses EXCEPT 
                    ![cid] = <<newColor, chameneoses[cid][2] + 1>>,
                    ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation – choose any non‑faded chameneos to act
\* ----------------------------------------------------------------------
Next == 
    \E c \in { i \in ChameneosesID : chameneoses[i][1] # Faded } : Meet(c)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety property required by the original description
\* ----------------------------------------------------------------------
SumMet == 
    numMeetings = N => 
        LET f == [c \in ChameneosesID |-> chameneoses[c][2]]
        IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

=============================================================================