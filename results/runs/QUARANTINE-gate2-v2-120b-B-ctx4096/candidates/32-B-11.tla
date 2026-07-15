---- MODULE Chameneos ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Helper: Recursive sum over a finite set
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and complement operation
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants (must be supplied by the .cfg)
\*   N – total number of meetings after which chameneoses fade
\*   M – number of chameneoses
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* State variables
\*   chameneoses : mapping from each id to a tuple (currentColor, meetingCount)
\*   meetingPlace : the id of the creature waiting at the mall, or a special
\*                  value meaning “empty”
\*   numMeetings : total number of completed meetings
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type invariant (kept for readability, not used by TLC directly)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in 0 .. N

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* Meet action for a given creature id (cid)
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
    /\ meetingPlace /= cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ chameneoses' =
         LET newColor == Complement(chameneoses[cid][1],
                                    chameneoses[meetingPlace][1])
         IN [chameneoses EXCEPT
               ![cid] = <<newColor, @[2] + 1>>,
               ![meetingPlace] = <<newColor, @[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation: any non‑faded creature may attempt to meet
\* ----------------------------------------------------------------------
Next ==
  /\ \E c \in { x \in ChameneosID : chameneoses[x][1] /= Faded } : Meet(c)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety property: when the prescribed number of meetings has been reached,
\* the total of individual meeting counters equals twice that number.
\* ----------------------------------------------------------------------
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====