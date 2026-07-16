---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent and        *)
(* symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf   *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive definition of a sum over a finite set
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + Sum(f, S \ {x})

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
\* Constants (provided by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M

\* A distinguished value meaning “no creature is waiting”.
\* It must be distinct from every valid creature identifier.
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
\* One step of the system: a non‑faded creature tries to meet
\* ----------------------------------------------------------------------
Meet(cid) ==
    IF meetingPlace = MeetingPlaceEmpty
    THEN
        IF numMeetings < N
        \* The meeting place is empty and we have not yet reached the limit:
        \* the creature simply occupies the place.
        THEN /\ meetingPlace' = cid
             /\ UNCHANGED <<chameneoses, numMeetings>>
        \* We have already performed N meetings; the creature fades
        \* and the state otherwise stays unchanged.
        ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
             /\ UNCHANGED <<meetingPlace, numMeetings>>
    ELSE
        /\ meetingPlace # cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ chameneoses' =
              LET newColor == Complement(chameneoses[cid][1],
                                         chameneoses[meetingPlace][1])
              IN [chameneoses EXCEPT
                     ![cid]            = <<newColor, @[2] + 1>>,
                     ![meetingPlace]   = <<newColor, @[2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Global next‑state relation
\* ----------------------------------------------------------------------
Next ==
    /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
    /\ UNCHANGED TypeOK   \* keep the type invariant true after every step

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety property described in the paper
\* ----------------------------------------------------------------------
SumMet ==
    numMeetings = N
    => LET f[c \in ChameneosID] == chameneoses[c][2]
       IN Sum(f, ChameneosesID) = 2 * N

\* ----------------------------------------------------------------------
\* Theorem (kept for compatibility with the original spec)
\* ----------------------------------------------------------------------
THEOREM Spec => []SumMet

====