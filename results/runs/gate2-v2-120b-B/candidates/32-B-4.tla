---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

\*---------------------------------------------------------------------*
\* Recursive definition to compute the sum of a function over a set.
\*---------------------------------------------------------------------*
RECURSIVE Sum(_, _)
Sum(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + Sum(f, S \ {x})

\*---------------------------------------------------------------------*
\* Colors and the special faded color.
\*---------------------------------------------------------------------*
Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

\*---------------------------------------------------------------------*
\* Complement of two distinct colors; if equal, returns the same color.
\*---------------------------------------------------------------------*
Complement(c1, c2) ==
  IF c1 = c2
  THEN c1
  ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\*---------------------------------------------------------------------*
\* Constants: N = total number of meetings after which chameneoses fade,
\*            M = number of chameneoses.
\*---------------------------------------------------------------------*
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

\*---------------------------------------------------------------------*
\* State variables.
\*---------------------------------------------------------------------*
VARIABLES chameneoses, meetingPlace, numMeetings

\*---------------------------------------------------------------------*
\* Convenience tuple of all variables.
\*---------------------------------------------------------------------*
vars == <<chameneoses, meetingPlace, numMeetings>>

\*---------------------------------------------------------------------*
\* Identifier set for chameneoses and a distinguished value meaning
\* “the meeting place is empty”.
\*---------------------------------------------------------------------*
ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

\*---------------------------------------------------------------------*
\* Type invariant.
\*---------------------------------------------------------------------*
TypeOK ==
  /\ chameneoses \in [ChameneosID -> (Color \cup {Faded}) \X (0 .. N)]
  /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}
  /\ numMeetings \in Nat

\*---------------------------------------------------------------------*
\* Initial state.
\*---------------------------------------------------------------------*
Init ==
  /\ chameneoses = [i \in ChameneosID |-> <<"blue", 0>>]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ numMeetings = 0

\*---------------------------------------------------------------------*
\* One chameneos (identified by cid) tries to meet.
\*---------------------------------------------------------------------*
Meet(cid) ==
  IF meetingPlace = MeetingPlaceEmpty THEN
    IF numMeetings < N THEN
      /\ meetingPlace' = cid
      /\ UNCHANGED <<chameneoses, numMeetings>>
    ELSE
      /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @ [2]>>]
      /\ UNCHANGED <<meetingPlace, numMeetings>>
  ELSE
    /\ meetingPlace /= cid
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ LET newColor == Complement(chameneoses[cid][1],
                                  chameneoses[meetingPlace][1])
       IN chameneoses' =
            [chameneoses EXCEPT
               ![cid] = <<newColor, @ [2] + 1>>,
               ![meetingPlace] = <<newColor, @ [2] + 1>>]
    /\ numMeetings' = numMeetings + 1

\*---------------------------------------------------------------------*
\* Next-state relation: any non‑faded chameneos may act.
\*---------------------------------------------------------------------*
Next ==
  \E c \in { i \in ChameneosID : chameneoses[i][1] # Faded } : Meet(c)

\*---------------------------------------------------------------------*
\* Full specification.
\*---------------------------------------------------------------------*
Spec == Init /\ [][Next]_vars

\*---------------------------------------------------------------------*
\* Property: when the required number of meetings has occurred, the total
\* count of individual meetings equals twice that number (each meeting
\* involves two chameneoses).
\*---------------------------------------------------------------------*
SumMet ==
  numMeetings = N =>
    LET f[c \in ChameneosID] == chameneoses[c][2]
    IN Sum(f, ChameneosID) = 2 * N

\*---------------------------------------------------------------------*
\* Theorem statement (kept unchanged).
\*---------------------------------------------------------------------*
THEOREM Spec => []SumMet

====