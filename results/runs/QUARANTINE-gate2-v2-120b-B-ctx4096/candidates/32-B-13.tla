---- MODULE Chameneos ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition for summing a function over a finite set
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and complementary color computation
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N (total meetings after which all fade) and M (number of
\* chameneoses). Both must be positive natural numbers.
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in Nat \ {0} /\ M \in Nat \ {0}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type invariant (used for debugging, not part of the safety spec)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ chameneoses \in [ChameneosesID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* Single step of the system when chameneos with identifier cid acts
\* ----------------------------------------------------------------------
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
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ LET newColor == Complement(chameneoses[cid][1],
                                 chameneoses[meetingPlace][1])
       IN chameneoses' =
            [chameneoses EXCEPT
               ![cid] = <<newColor, @[2] + 1>>,
               ![meetingPlace] = <<newColor, @[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Stutter step: when all chameneoses have faded the system does nothing.
\* This makes the next-state relation total, eliminating the TLC error.
\* ----------------------------------------------------------------------
Stutter ==
  /\ \A i \in ChameneosesID : chameneoses[i][1] = Faded
  /\ UNCHANGED <<chameneoses, meetingPlace, numMeetings>>

\* ----------------------------------------------------------------------
\* Overall next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E c \in { i \in ChameneosesID : chameneoses[i][1] # Faded } : Meet(c)
  \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Property: when the total number of meetings reaches N, the sum of the
\* individual meeting counters equals 2 * N.
\* ----------------------------------------------------------------------
SumMet ==
  /\ numMeetings = N
  /\ LET f[c \in ChameneosesID] == chameneoses[c][2]
     IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====