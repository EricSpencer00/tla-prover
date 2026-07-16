---- MODULE Chameneos ----
EXTENDS Integers

\* Recursive definition for summing a function over a set
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* Colors used by the chameneoses
Color == {"blue", "red", "yellow"}

\* Choose a special value that is not a color to represent the faded state
Faded == CHOOSE c : c \notin Color

\* Complement of two different colors, or the same color if they are equal
Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* Parameters:
\* N – total number of meetings after which chameneoses fade
\* M – number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

\* Helper tuple of the three state variables
vars == <<chameneoses, meetingPlace, numMeetings>>

\* Identifier set for the chameneoses
ChameneosID == 1 .. M

\* Special value representing an empty meeting place
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* Type correctness predicate
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in 0 .. N

\* Initial state: all chameneoses start blue with 0 meetings, meeting place empty, 0 meetings done
Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* Action for a chameneos with identifier cid to try to meet
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    \* The meeting place is empty
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @(cid)[2]>>]
      /\ UNCHANGED <<meetingPlace, numMeetings>>
  ELSE
    \* The meeting place already contains another chameneos
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ chameneoses' =
         LET newColor == Complement(chameneoses[cid][1],
                                   chameneoses[meetingPlace][1])
         IN [chameneoses EXCEPT
                ![cid] = <<newColor, @(cid)[2] + 1>>,
                ![meetingPlace] = <<newColor, @(meetingPlace)[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* Next-state relation: pick any non‑faded chameneos to attempt a meeting
Next ==
  /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
  /\ UNCHANGED <<>>

\* Full specification
Spec == Init /\ [][Next]_vars

\* Desired safety property: when the system has performed N meetings,
\* the sum of all individual meeting counters equals 2*N
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====