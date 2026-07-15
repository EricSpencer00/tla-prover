---- MODULE Chameneos ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition of a sum over a function and a finite set.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors used by the chameneoses.
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}

\* The special “faded” color is any value not in the set of normal colors.
Faded == CHOOSE c : c \notin Color

\* Complementary color according to the specification.
Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N = total number of meetings after which everyone fades,
\*            M = number of chameneoses.
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M

\* A distinguished value meaning “the meeting place is empty”.
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

\* ----------------------------------------------------------------------
\* Type correctness invariant.
\* ----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ChameneosesID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in (0 .. N)

\* ----------------------------------------------------------------------
\* Initial state: each chameneos starts with a blue color and zero meetings,
\* the meeting place is empty, and no meetings have occurred yet.
\* ----------------------------------------------------------------------
Init ==
  /\ chameneoses = [i \in ChameneosesID |-> <<"blue", 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* One chameneos (identified by cid) attempts to meet.
\* ----------------------------------------------------------------------
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    \* No one is waiting: the chameneos either enters the meeting place
    \* (if we have not yet reached the limit N) or, when N is already
    \* reached, it simply fades and stays outside.
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
      /\ UNCHANGED <<meetingPlace, numMeetings>>
  ELSE
    \* Someone is already waiting; they must be different chameneoses.
    /\ meetingPlace /= cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ LET newColor == Complement(chameneoses[cid][1],
                                 chameneoses[meetingPlace][1])
       IN chameneoses' =
            [chameneoses EXCEPT
               ![cid]            = <<newColor, @[2] + 1>>,
               ![meetingPlace]   = <<newColor, @[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation: any non‑faded chameneos may try to meet.
\* ----------------------------------------------------------------------
Next ==
  \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } :
    Meet(c)

\* ----------------------------------------------------------------------
\* Full specification.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Intended safety property: when the global meeting counter reaches N,
\* the sum of the individual meeting counters equals 2·N.
\* ----------------------------------------------------------------------
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosesID] == chameneoses[c][2]
    IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====