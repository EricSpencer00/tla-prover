---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition of a finite sum over a finite set.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors and the special faded color.
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

\* ----------------------------------------------------------------------
\* Complement rule: if the two colors are equal, the result is that color;
\* otherwise pick the third one.
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N – total number of meetings after which chameneoses fade,
\*            M – number of chameneoses.
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

\* ----------------------------------------------------------------------
\* Derived names for readability.
\* ----------------------------------------------------------------------
vars == <<chameneoses, meetingPlace, numMeetings>>
ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type invariant.
\* ----------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}

\* ----------------------------------------------------------------------
\* Initial state.
\* ----------------------------------------------------------------------
Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* Action for a single chameneos (identified by cid) attempting to meet.
\* ----------------------------------------------------------------------
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty THEN
      /\ numMeetings < N
          \* The mall is empty and we have not yet reached the meeting limit:
          \* the chameneos simply occupies the meeting place.
          /\ meetingPlace' = cid
          /\ UNCHANGED <<chameneoses, numMeetings>>
      \/ /\ numMeetings >= N
          \* The meeting limit has been reached; the chameneos fades.
          /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
          /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE
      /\ meetingPlace /= cid
          \* A second chameneos arrives; they both mutate.
          /\ meetingPlace' = MeetingPlaceEmpty
          /\ LET newColor == Complement(chameneoses[cid][1],
                                        chameneoses[meetingPlace][1])
             IN chameneoses' =
                [chameneoses EXCEPT
                     ![cid] = <<newColor, @[2] + 1>>,
                     ![meetingPlace] = <<newColor, @[2] + 1>>]
          /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Next-state relation: any non‑faded chameneos may try to meet.
\* ----------------------------------------------------------------------
Next ==
   /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] # Faded } : Meet(c)
   /\ UNCHANGED meetingPlace \cup numMeetings \cup chameneoses

\* ----------------------------------------------------------------------
\* Full specification.
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety invariant: upon termination the total number of individual
\* meetings equals twice the number of global meetings (2 * N).
\* ----------------------------------------------------------------------
SumMet ==
   /\ numMeetings = N
   /\ LET f[c \in ChameneosesID] == chameneoses[c][2]
      IN Sum(f, ChameneosesID) = 2 * N

\* ----------------------------------------------------------------------
\* Theorem (kept for compatibility with the original file).
\* ----------------------------------------------------------------------
THEOREM Spec => []SumMet

====