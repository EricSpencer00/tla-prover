---- MODULE Chameneos ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition of Sum over a finite set S of identifiers, using a
\* function f that maps each identifier to a natural number.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\*----------------------------------------------------------------------
\* Colours used by the chameneoses.  A special colour "Faded" is used to
\* denote a chameneos that has terminated its participation.
\*----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

\*----------------------------------------------------------------------
\* Complement of two different colours: the third colour of the set.
\*----------------------------------------------------------------------
Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\*----------------------------------------------------------------------
\* Constants:
\*   N – total number of meetings after which chameneoses fade.
\*   M – number of chameneoses.
\*----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\*----------------------------------------------------------------------
\* Variables:
\*   chameneoses   – a function mapping each chameneos identifier to a
\*                   pair <<colour, meetingCount>>.
\*   meetingPlace  – either a chameneos identifier that is waiting, or a
\*                   distinguished value meaning “empty”.
\*   numMeetings   – total number of completed meetings.
\*----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\*----------------------------------------------------------------------
\* Type correctness invariant.
\*----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in Nat

\*----------------------------------------------------------------------
\* Initial state: every chameneos starts with colour "blue" and zero
\* meetings; the meeting place is empty; no meetings have occurred.
\*----------------------------------------------------------------------
Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\*----------------------------------------------------------------------
\* One step of the system, parameterised by the identifier of the chameneos
\* that attempts to act (cid).  The action respects the intended protocol:
\*   * If the meeting place is empty and the total number of meetings has not
\*     reached N, the chameneos occupies the place.
\*   * If the meeting place is empty but N meetings have already occurred,
\*     the chameneos fades (its colour changes to Faded) and no other
\*     variable changes.
\*   * If the meeting place already holds a different chameneos, the two
\*     meet: both change to the complementary colour, both increment their
\*     personal meeting counters, the global meeting counter increases, and the
\*     meeting place becomes empty again.
\*----------------------------------------------------------------------
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty
  THEN
    IF numMeetings < N
    THEN /\ meetingPlace' = cid
         /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
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

\*----------------------------------------------------------------------
\* The system repeatedly lets any non‑faded chameneos attempt to act.
\*----------------------------------------------------------------------
Next ==
  /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
  /\ UNCHANGED vars

\*----------------------------------------------------------------------
\* Overall specification: initial condition and stuttering‑closed Next.
\*----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*----------------------------------------------------------------------
\* Property stating that when the required number of meetings N has been
\* reached, the sum of the individual meeting counters equals 2 * N.
\*----------------------------------------------------------------------
SumMet ==
  numMeetings = N
  => LET f[c \in ChameneosesID] == chameneoses[c][2]
     IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

=============================================================================