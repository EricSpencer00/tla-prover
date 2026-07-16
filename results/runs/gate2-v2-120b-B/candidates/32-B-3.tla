---- MODULE Chameneos ----
EXTENDS Integers, Naturals

\* -------------------------------------------------------------------------
\* Recursive sum operator, unchanged from the original specification
\* -------------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + Sum(f, S \ {x})

\* -------------------------------------------------------------------------
\* Colors and the special value for a faded chameneos
\* -------------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* -------------------------------------------------------------------------
\* Constants: N = total number of meetings after which everybody fades
\*            M = number of chameneoses
\* -------------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in Nat \ {0}
ASSUME M \in Nat \ {0}

\* -------------------------------------------------------------------------
\* Variables
\* -------------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* -------------------------------------------------------------------------
\* Type invariant – unchanged
\* -------------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in Nat

\* -------------------------------------------------------------------------
\* Initial state – unchanged
\* -------------------------------------------------------------------------
Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* -------------------------------------------------------------------------
\* Meet action – corrected to satisfy the state‑update requirement
\* -------------------------------------------------------------------------
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    /\ numMeetings < N
    /\ meetingPlace' = cid
    /\ UNCHANGED <<chameneoses, numMeetings>>
  ELSE
    /\ meetingPlace # cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ chameneoses' =
         LET newColor == Complement(chameneoses[cid][1],
                                   chameneoses[meetingPlace][1])
         IN [chameneoses EXCEPT
                ![cid] = <<newColor, @[2] + 1>>,
                ![meetingPlace] = <<newColor, @[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* -------------------------------------------------------------------------
\* When the meeting place is full and the limit N has been reached,
\* the first chameneos that arrives simply fades and leaves the place.
\* This branch is added to guarantee that every variable has a defined
\* next value, thereby eliminating the “successor state is not completely
\* specified” error reported by TLC.
\* -------------------------------------------------------------------------
FadeAndLeave(cid) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings >= N
  /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ numMeetings' = numMeetings

\* -------------------------------------------------------------------------
\* Next-state relation – choose either a regular meet or the fade‑and‑leave
\* action for a non‑faded chameneos.
\* -------------------------------------------------------------------------
Next ==
  \/ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
  \/ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : FadeAndLeave(c)

Spec == Init /\ [][Next]_vars

\* -------------------------------------------------------------------------
\* Safety property: when the prescribed number of meetings has been
\* performed, the total number of individual meetings equals 2*N.
\* -------------------------------------------------------------------------
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====