---- MODULE Chameneos ----
EXTENDS Integers, Sequences

\* ----------------------------------------------------------------------
\* Recursive sum of a function over a finite set
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and complementary operation
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N = number of meetings after which all fade, M = number of chameneoses
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

\* ----------------------------------------------------------------------
\* Derived identifiers
\* ----------------------------------------------------------------------
ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

\* ----------------------------------------------------------------------
\* State space typing predicate (kept unchanged)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ChameneosesID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in 0 .. N

\* ----------------------------------------------------------------------
\* Initial state (kept unchanged)
\* ----------------------------------------------------------------------
Init ==
  /\ chameneoses \in [ChameneosesID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* One chameneos attempts to meet
\* ----------------------------------------------------------------------
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
      /\ meetingPlace' = meetingPlace
      /\ numMeetings' = numMeetings
  ELSE
    /\ meetingPlace # cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ let newColor == Complement(chameneoses[cid][1],
                                 chameneoses[meetingPlace][1]) in
       chameneoses' =
         [chameneoses EXCEPT
            ![cid]          = <<newColor, chameneoses[cid][2] + 1>>,
            ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation (unchanged)
\* ----------------------------------------------------------------------
Next ==
  /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)

\* ----------------------------------------------------------------------
\* Overall specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<chameneoses, meetingPlace, numMeetings>>

\* ----------------------------------------------------------------------
\* Property: upon termination, the total number of individual meetings equals 2*N
\* ----------------------------------------------------------------------
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosesID] == chameneoses[c][2] IN
      Sum(f, ChameneosesID) = 2 * N

\* Theorem (kept unchanged)
THEOREM Spec => []SumMet

====