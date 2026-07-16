---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition of a finite sum over a function f on a finite set S
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and their complement
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
\* Faded is a distinguished value not belonging to the set of colors.
Faded == CHOOSE c : c \notin Color

\* Complement returns the unchanged color when the two are equal,
\* otherwise it returns the unique third color.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N – number of meetings after which chameneoses fade;
\*            M – number of chameneoses
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

\* Convenience tuple of the three variables
vars == <<chameneoses, meetingPlace, numMeetings>>

\* Identifier set for the chameneoses
ChameneosesID == 1 .. M

\* A distinguished value meaning “no creature is waiting”.
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* One chameneos (identified by cid) attempts to meet
\* ----------------------------------------------------------------------
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty THEN
        \* No one is waiting: either enter the meeting place,
        \* or, if the total number of meetings has already reached N,
        \* fade immediately.
        IF numMeetings < N THEN
              /\ meetingPlace' = cid
              /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE
              /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
              /\ meetingPlace' = MeetingPlaceEmpty
              /\ UNCHANGED numMeetings
   ELSE
        \* Someone is waiting: perform a meeting, then leave the place empty.
        /\ meetingPlace /= cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN chameneoses' =
                 [chameneoses EXCEPT
                      ![cid] = <<newColor, chameneoses[cid][2] + 1>>,
                      ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* The system repeatedly lets any non‑faded chameneos try to meet.
\* ----------------------------------------------------------------------
Next ==
   /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
   /\ UNCHANGED meetingPlace \cup {numMeetings} \cup {chameneoses}
   \* (the above line is just syntactic sugar to keep the
   \*  action total; the actual variable updates are inside Meet)

\* ----------------------------------------------------------------------
\* Overall specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Upon termination (numMeetings = N), the total number of individual
\* meetings equals 2·N.
\* ----------------------------------------------------------------------
SumMet ==
   /\ numMeetings = N
   /\ LET f[c \in ChameneosID] == chameneoses[c][2]
      IN Sum(f, ChameneosesID) = 2 * N

THEOREM Spec => []SumMet

====