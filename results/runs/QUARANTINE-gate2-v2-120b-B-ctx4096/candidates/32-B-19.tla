---- MODULE Chameneos ----
EXTENDS Integers, Sequences

\* ----------------------------------------------------------------------
\* Recursive definition of Sum over a function f on a finite set S.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and auxiliary definitions.
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == "Faded"               \* a concrete value to represent the faded color

Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants.
\* N – total number of meetings after which chameneoses fade.
\* M – number of chameneoses.
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* Variables.
\* chameneoses : a function ChameneosID -> (color, meetingCount)
\* meetingPlace : either a chameneos identifier or a distinguished empty value
\* numMeetings   : total number of completed meetings
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

ChameneosID == 1 .. M
MeetingPlaceEmpty == 0          \* a concrete integer not in ChameneosID

\* ----------------------------------------------------------------------
\* Type correctness (kept for readability, not used as an invariant).
\* ----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in 0 .. N

\* ----------------------------------------------------------------------
\* Initial state.
\* ----------------------------------------------------------------------
Init ==
  /\ chameneoses = [i \in ChameneosID |-> <<"blue", 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings   = 0

\* ----------------------------------------------------------------------
\* One chameneos (cid) attempts to meet.
\* ----------------------------------------------------------------------
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
      /\ UNCHANGED <<meetingPlace, numMeetings>>
  ELSE
    /\ meetingPlace # cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ LET newColor == Complement(chameneoses[cid][1],
                                 chameneoses[meetingPlace][1])
       IN chameneoses' =
            [chameneoses EXCEPT
               ![cid]          = <<newColor, chameneoses[cid][2] + 1>>,
               ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation: any non‑faded chameneos may try to meet.
\* ----------------------------------------------------------------------
Next ==
  \E c \in { i \in ChameneosID : chameneoses[i][1] # Faded } : Meet(c)

\* ----------------------------------------------------------------------
\* Full specification.
\* ----------------------------------------------------------------------
vars == <<chameneoses, meetingPlace, numMeetings>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Property: when exactly N meetings have occurred, the sum of individual
\* meeting counts equals 2 * N (each meeting involves two chameneoses).
\* ----------------------------------------------------------------------
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====