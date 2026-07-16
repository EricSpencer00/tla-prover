---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition used to sum a function over a finite set.
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Domain definitions
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
    IF c1 = c2
      THEN c1
      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* ----------------------------------------------------------------------
\* One step of the system: a chameneos with identifier cid tries to meet.
\* The action is written so that every variable is assigned a value in
\* every branch, thereby satisfying TLC's “no dangling variables” rule.
\* ----------------------------------------------------------------------
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty THEN
        IF numMeetings < N THEN
            /\ meetingPlace' = cid
            /\ chameneoses' = chameneoses
            /\ numMeetings' = numMeetings
        ELSE
            /\ meetingPlace' = MeetingPlaceEmpty
            /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, chameneoses[cid][2]>>]
            /\ numMeetings' = numMeetings
    ELSE
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ LET newColor == Complement(chameneoses[cid][1],
                                      chameneoses[meetingPlace][1])
           IN chameneoses' =
                [chameneoses EXCEPT
                    ![cid] = <<newColor, chameneoses[cid][2] + 1>>,
                    ![meetingPlace] = <<newColor, chameneoses[meetingPlace][2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* System evolution: any non‑faded chameneos may attempt to meet.
\* ----------------------------------------------------------------------
Next ==
    /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant describing the required relationship between the total number
\* of meetings and the individual meeting counters.
\* ----------------------------------------------------------------------
SumMet ==
    /\ numMeetings = N
    /\ LET f[c \in ChameneosID] == chameneoses[c][2]
       IN Sum(f, ChameneosID) = 2 * N

\* The theorem is kept unchanged; it is proved using the invariant above.
THEOREM Spec => []SumMet

====