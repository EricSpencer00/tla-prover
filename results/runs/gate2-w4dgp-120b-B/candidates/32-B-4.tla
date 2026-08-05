---- MODULE Chameneos ----
(***************************************************************************)
(* A specification of a 'concurrency game' requiring concurrent            *)
(* and symmetrical cooperation - https://cedric.cnam.fr/fichiers/RC474.pdf *)
(***************************************************************************)
EXTENDS Integers

\* Recursive Sum() is used in the SumMet property below.
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

\* Complement two colors, yielding a third distinct color if they differ.
Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* N - number of meetings after which chameneoses fade; M - number of them.
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLES chameneoses, meetingPlace, numMeetings
vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

\* For each chameneos, keep its current color and how many meetings it has
\* participated in; meetingPlace remembers the chameneos waiting to meet.
TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* A chameneos enters the (empty) meeting place; if the meeting limit is
\* reached it instead fades and does not enter.
Enter(cid) ==
   /\ meetingPlace = MeetingPlaceEmpty
   /\ meetingPlace' = cid
   /\ UNCHANGED <<chameneoses, numMeetings>>

Fade(cid) ==
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = N
   /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @(2) >>]
   /\ UNCHANGED <<meetingPlace, numMeetings>>

\* Two chameneoses in the meeting place meet and mutate their colors.
Meet(cid) ==
   /\ meetingPlace # MeetingPlaceEmpty
   /\ meetingPlace # cid
   /\ meetingPlace' = MeetingPlaceEmpty
   /\ numMeetings' = numMeetings + 1
   /\ LET newColor == Complement(chameneoses[cid][1],
                                 chameneoses[meetingPlace][1])
          ch == [ newColor, chameneoses[cid][2] + 1 ]
      IN chameneoses' = [chameneoses EXCEPT ![cid] = ch, ![meetingPlace] = ch]

Next ==
   \/ \E c \in ChameneosesID : Enter(c) \/ Fade(c) \/ Meet(c)

Spec == Init /\ [][Next]_vars

\* When the limit is reached, the total number of individual meetings is
\* exactly twice the number of meetings (each meeting involves two chameneoses).
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet

====