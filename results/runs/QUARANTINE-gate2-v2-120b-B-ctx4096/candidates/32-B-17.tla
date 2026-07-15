---- MODULE Chameneos ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive sum used in the invariant
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and complement operation
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == 
    IF c1 = c2 THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

vars == <<chameneoses, meetingPlace, numMeetings>>

\* ----------------------------------------------------------------------
\* Type invariant (kept unchanged)
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
\* Meet action – rewritten to assign every variable in every branch
\* ----------------------------------------------------------------------
Meet(cid) == 
    IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
            /\ meetingPlace' = cid
            /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE
            /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
            /\ meetingPlace' = meetingPlace
            /\ UNCHANGED numMeetings
    ELSE
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ chameneoses' = 
            LET newColor == Complement(chameneoses[cid][1],
                                       chameneoses[meetingPlace][1])
            IN [chameneoses EXCEPT 
                    ![cid] = <<newColor, chameneoses[cid][2] + 1>>,
                    ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next action – chooses a non‑faded chameneos to try to meet
\* ----------------------------------------------------------------------
Next == 
    /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
    /\ UNCHANGED TypeOK

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant required by the original description
\* ----------------------------------------------------------------------
SumMet == 
    numMeetings = N => 
        LET f[c \in ChameneosID] == chameneoses[c][2]
        IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====