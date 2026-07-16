---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Recursive sum over a finite set of identifiers
\* ----------------------------------------------------------------------
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) ==
    IF c1 = c2
    THEN c1
    ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* ----------------------------------------------------------------------
\* Constants: N - total number of meetings after which chameneoses fade
\*            M - number of chameneoses
\* ----------------------------------------------------------------------
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings

\* ----------------------------------------------------------------------
\* Convenience tuple
\* ----------------------------------------------------------------------
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\* ----------------------------------------------------------------------
\* Type invariant (useful for TLC, not part of the safety property)
\* ----------------------------------------------------------------------
TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}

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
        \* No one is waiting
        IF numMeetings < N THEN
             /\ meetingPlace' = cid
             /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE
             \* The system has already performed N meetings; the chameneos
                fades and all state stays unchanged.
             /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
             /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE
        \* There is a waiting chameneos (meetingPlace) different from cid
        /\ meetingPlace /= cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ chameneoses' =
               LET newColor == Complement(chameneoses[cid][1],
                                          chameneoses[meetingPlace][1])
               IN [chameneoses EXCEPT
                       ![cid]          = <<newColor, @[2] + 1>>,
                       ![meetingPlace] = <<newColor, @[2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* ----------------------------------------------------------------------
\* Global next-state relation: any non‑faded chameneos may act
\* ----------------------------------------------------------------------
Next ==
   /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
   /\ UNCHANGED TypeOK   \* keep the type invariant unchanged (no effect on behavior)

\* ----------------------------------------------------------------------
\* Full specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Desired safety property: when the system stops after N meetings,
\* the total number of individual meetings equals 2·N
\* ----------------------------------------------------------------------
SumMet ==
    numMeetings = N =>
        LET f[c \in ChameneosID] == chameneoses[c][2]
        IN Sum(f, ChameneosID) = 2 * N

=============================================================================