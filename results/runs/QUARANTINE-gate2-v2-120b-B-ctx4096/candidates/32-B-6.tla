---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)

EXTENDS Integers

\* ------------------------------------------------------------------------
\* Recursive sum over a finite set, used in the invariant.
\* ------------------------------------------------------------------------
RECURSIVE Sum(_,_)
Sum(f, S) == 
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

\* ------------------------------------------------------------------------
\* Colors and the special faded value.
\* ------------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == 
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ------------------------------------------------------------------------
\* Constants describing the size of the game.
\* ------------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ------------------------------------------------------------------------
\* State variables.
\* ------------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

\* Group them for convenience.
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

\* ------------------------------------------------------------------------
\* Type correctness predicate.
\* ------------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

\* ------------------------------------------------------------------------
\* Initial state.
\* ------------------------------------------------------------------------
Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* ------------------------------------------------------------------------
\* A single meeting step initiated by chameneos cid.
\* ------------------------------------------------------------------------
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty THEN
      IF numMeetings < N THEN
         /\ meetingPlace' = cid
         /\ UNCHANGED <<chameneoses, numMeetings>>
      ELSE
         /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
         /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE
      /\ meetingPlace /= cid
      /\ meetingPlace' = MeetingPlaceEmpty
      /\ chameneoses' =
            LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
            IN [chameneoses EXCEPT
                   ![cid] = <<newColor, chameneoses[cid][2] + 1>>,
                   ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
      /\ numMeetings' = numMeetings + 1

\* ------------------------------------------------------------------------
\* Next-state relation: any non‑faded chameneos may try to meet.
\* ------------------------------------------------------------------------
Next ==
   /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)

\* ------------------------------------------------------------------------
\* Full specification.
\* ------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ------------------------------------------------------------------------
\* Invariant required by the original paper.
\* ------------------------------------------------------------------------
SumMet ==
   numMeetings = N =>
      LET f[c \in ChameneosID] == chameneoses[c][2]
      IN Sum(f, ChameneosID) = 2 * N

\* ------------------------------------------------------------------------
\* Theorem stating that the invariant holds throughout all behaviors.
\* ------------------------------------------------------------------------
THEOREM Spec => []SumMet

====