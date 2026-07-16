---- MODULE Chameneos ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Auxiliary recursive definition for summing a function over a set
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + Sum(f, S \ {x})

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
\* Constants (must be provided in the .cfg file)
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
\* Type correctness invariant (kept unchanged)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* Helper that determines the new color after a meeting
\* ----------------------------------------------------------------------
NewColor(c1, c2) == Complement(c1, c2)

\* ----------------------------------------------------------------------
\* Meet action corrected to assign all variables in every branch
\* ----------------------------------------------------------------------
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ chameneoses' = chameneoses
      /\ numMeetings' = numMeetings
    ELSE
      /\ meetingPlace' = meetingPlace
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
      /\ numMeetings' = numMeetings
  ELSE
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ numMeetings' = numMeetings + 1
    /\ chameneoses' =
         LET newC == NewColor(chameneoses[cid][1], chameneoses[meetingPlace][1])
         IN [chameneoses EXCEPT
                ![cid] = <<newC, chameneoses[cid][2] + 1>>,
                ![meetingPlace] = <<newC, chameneoses[meetingPlace][2] + 1>>]

\* ----------------------------------------------------------------------
\* Next-state relation: any non‑faded chameneos may attempt to meet
\* ----------------------------------------------------------------------
Next ==
  /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
  /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Desired property: when N meetings have occurred, the total number of
\* individual meetings equals 2*N.
\* ----------------------------------------------------------------------
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

=============================================================================