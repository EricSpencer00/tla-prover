---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

-----------------------------------------------------------------------------

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

-----------------------------------------------------------------------------

\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in Nat \ {0} /\ M \in Nat \ {0}

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in Nat

Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* A single chameneos attempts to use the meeting place.
\* If the place is empty and the overall meeting limit has not been reached,
\*   it simply occupies the place.
\* If the limit has been reached, the chameneos that tries to enter
\*   immediately fades (its color becomes Faded) and the rest of the state
\*   stays unchanged.
\* If the place is already occupied by a different chameneos, the two meet:
\*   they both acquire the complementary color, increment their personal
\*   meeting counters, the meeting place becomes empty again, and the global
\*   meeting counter is increased.
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
      /\ LET newColor == Complement(chameneoses[cid][1],
                                   chameneoses[meetingPlace][1])
         IN chameneoses' =
               [chameneoses EXCEPT
                  ![cid] = <<newColor, @[2] + 1>>,
                  ![meetingPlace] = <<newColor, @[2] + 1>>]
      /\ numMeetings' = numMeetings + 1

\* Non‑faded chameneoses repeatedly try to enter the meeting place.
Next ==
   \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------

\* Upon termination, the sum of the (individual) meetings that all chameneoses have
\* been in, is equal to 2 * N.
SumMet ==
   /\ numMeetings = N
   /\ LET f[c \in ChameneosID] == chameneoses[c][2]
      IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet

====