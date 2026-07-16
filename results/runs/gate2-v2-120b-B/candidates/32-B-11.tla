---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition used later for the invariant
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Domain definitions
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants (to be given concrete values in the .cfg)
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type invariant (helps TLC but does not affect behavior)
\* ----------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
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
\* One-step action for a chameneos with identifier cid
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
      /\ meetingPlace /= cid
      /\ meetingPlace' = MeetingPlaceEmpty
      /\ LET newColor == Complement(chameneoses[cid][1],
                                    chameneoses[meetingPlace][1])
         IN  chameneoses' =
                [chameneoses EXCEPT
                   ![cid]          = <<newColor, chameneoses[cid][2] + 1>>,
                   ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
      /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Stutter step to keep the model from deadlocking when all are faded
\* ----------------------------------------------------------------------
Stutter ==
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings >= N
   /\ UNCHANGED <<chameneoses, meetingPlace, numMeetings>>

\* ----------------------------------------------------------------------
\* Main next-state relation
\* ----------------------------------------------------------------------
Next ==
   \/ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
   \/ Stutter

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant relating total meetings to parameter N
\* ----------------------------------------------------------------------
SumMet == numMeetings = N => LET f[c \in ChameneosID] == chameneoses[c][2]
                             IN Sum(f, ChameneosID) = 2 * N

=============================================================================