----------------------------- MODULE Chameneos -----------------------------
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* -----------------------------------------------------------------------
\* Recursive sum operator over a finite set of identifiers
\* -----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\* -----------------------------------------------------------------------
\* Colors and helper definitions
\* -----------------------------------------------------------------------
Color   == {"blue", "red", "yellow"}
Faded   == CHOOSE c : c \notin Color

Complement(c1, c2) ==
  IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* -----------------------------------------------------------------------
\* Constants (to be supplied in the .cfg file)
\* -----------------------------------------------------------------------
\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* -----------------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

\* Tuple of all variables, used for the stuttering operator [_]_vars
vars == <<chameneoses, meetingPlace, numMeetings>>

\* Identifier domain for chameneoses
ChameneosID == 1 .. M

\* A distinguished value meaning “no chameneos is waiting in the meeting place”
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* -----------------------------------------------------------------------
\* Type correctness predicate (useful for debugging, not part of the spec)
\* -----------------------------------------------------------------------
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in (0 .. N)

\* -----------------------------------------------------------------------
\* Initial state
\* -----------------------------------------------------------------------
Init ==
  /\ chameneoses \in [ChameneosID -> Color \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\* -----------------------------------------------------------------------
\* Action for a particular chameneos (cid) trying to meet
\* -----------------------------------------------------------------------
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    \* No one is waiting; this chameneos becomes the waiting one,
    \* unless the global meeting limit has been reached.
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      \* The limit has been reached; the chameneos that would have entered
      \* simply fades and the state otherwise does not change.
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
      /\ UNCHANGED <<meetingPlace, numMeetings>>
  ELSE
    \* Another chameneos is already waiting; they meet and both fade
    \* (or change color) according to the Complement function.
    /\ meetingPlace /= cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ chameneoses' =
         LET newColor == Complement(chameneoses[cid][1],
                                   chameneoses[meetingPlace][1])
         IN [chameneoses EXCEPT
               ![cid]          = <<newColor, @[2] + 1>>,
               ![meetingPlace] = <<newColor, @[2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\* -----------------------------------------------------------------------
\* Overall Next action: any non‑faded chameneos may attempt to meet
\* -----------------------------------------------------------------------
Next ==
  /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } :
       Meet(c)

\* -----------------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* -----------------------------------------------------------------------
\* Desired invariant: when the global meeting counter reaches N,
\* the sum of individual meeting counts equals 2·N.
\* -----------------------------------------------------------------------
SumMet ==
  numMeetings = N =>
    LET f == [c \in ChameneosID |-> chameneoses[c][2]]
    IN Sum(f, ChameneosID) = 2 * N

\* -----------------------------------------------------------------------
\* Theorem stating that the invariant holds throughout all behaviors
\* -----------------------------------------------------------------------
THEOREM Spec => []SumMet

=============================================================================