---- MODULE Chameneos ----
EXTENDS Integers

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color

Complement(c1, c2) == IF c1 = c2
                      THEN c1
                      ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}

Init == /\ chameneoses \in [ChameneosesID -> Color \X {0}]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ numMeetings = 0

\* A meeting takes place when exactly one other chameneoses creature is waiting.
\* A chameneoses creature at the meeting place that is not yet faded performs
\* one of the following: enters an empty meeting place, takes on the faded
\* color (at the end of the game), or meets another waiting creature and takes
\* on the complementary color.
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty
      THEN IF numMeetings < N
              THEN /\ meetingPlace' = cid
                   /\ UNCHANGED <<chameneoses, numMeetings>>
              ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                   /\ UNCHANGED <<meetingPlace, numMeetings>>
      ELSE /\ meetingPlace # cid
           /\ meetingPlace' = MeetingPlaceEmpty
           /\ numMeetings' = numMeetings + 1
           /\ chameneoses' =
                 LET newColor == Complement(chameneoses[cid][1],
                                            chameneoses[meetingPlace][1])
                 IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                          ![meetingPlace] = <<newColor, @[2] + 1>>]

Next == \E c \in { x \in ChameneosesID : chameneoses[x][1] /= Faded} : Meet(c)

Spec == Init /\ [][Next]_vars

\* The grand total of individual meetings equals twice the number of meetings,
\* which is the full termination condition in the original paper's game model.
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet
====