---- MODULE Chameneos ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive function to compute the sum of a function f over a set S.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

\*---------------------------------------------------------------------*
\* Colors and auxiliary definitions
\*---------------------------------------------------------------------*
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\*---------------------------------------------------------------------*
\* Constants
\*---------------------------------------------------------------------*
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\*---------------------------------------------------------------------*
\* Variables
\*---------------------------------------------------------------------*
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\*---------------------------------------------------------------------*
\* Type invariant
\*---------------------------------------------------------------------*
TypeOK ==
    /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
    /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
    /\ numMeetings \in 0 .. N

\*---------------------------------------------------------------------*
\* Initial state
\*---------------------------------------------------------------------*
Init ==
    /\ chameneoses \in [ChameneosID -> Color \X {0}]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ numMeetings = 0

\*---------------------------------------------------------------------*
\* Action for a single chameneos attempting to meet
\*---------------------------------------------------------------------*
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
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN chameneoses' =
                [chameneoses EXCEPT
                    ![cid] = <<newColor, @[2] + 1>>,
                    ![meetingPlace] = <<newColor, @[2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\*---------------------------------------------------------------------*
\* Global next-state action
\*---------------------------------------------------------------------*
Next ==
    /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
    /\ UNCHANGED vars \ meetingPlace \ numMeetings \ chameneoses

Spec == Init /\ [][Next]_vars

\*---------------------------------------------------------------------*
\* Safety property: when N meetings have occurred, the total number of
\* individual meetings recorded equals 2*N.
\*---------------------------------------------------------------------*
SumMet ==
    (numMeetings = N) =>
        LET f[c \in ChameneosID] == chameneoses[c][2]
        IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====