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

\* N - number of total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})

VARIABLE chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ ChameneosID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosID \cup {MeetingPlaceEmpty}

Init == /\ chameneoses \in [ChameneosID -> Color \X {0}]
        /\ meetingPlace = MeetingPlaceEmpty
        /\ numMeetings = 0

\* A chameneoses enters a meeting place.  If the meeting place is not empty, a
\* meeting with the waiting chameneoses takes place and both chameneoses mutate.
\* Repeatedly try to enter the meeting place for chameneoses that are not faded
\* yet.  The system terminates once the color of all chameneoses is faded.
Meet(cid) == /\ meetingPlace = MeetingPlaceEmpty
              /\ IF numMeetings < N
                    THEN /\ meetingPlace' = cid
                         /\ UNCHANGED <<chameneoses, numMeetings>>
                    ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
                         /\ UNCHANGED <<meetingPlace, numMeetings>>
              /\ meetingPlace # MeetingPlaceEmpty
              /\ meetingPlace' = MeetingPlaceEmpty
              /\ meetingPlace # cid
              /\ LET newColor == Complement(chameneoses[cid][1],
                                            chameneoses[meetingPlace][1])
                 IN chameneoses' = [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                                    ![meetingPlace] = <<newColor, @[2] + 1>>]
              /\ numMeetings' = numMeetings + 1

Next == /\ \E c \in { x \in ChameneosID : chameneoses[x][1] # Faded } : Meet(c)
        /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the (individual) meetings that all chameneoses
\* have been in is equal to 2*N.  It is *not* guaranteed that all chameneoses
\* have been in a meeting with another chameneoses.  See section A. Game
\* termination on page 5 of the original paper.
SumMet == numMeetings = N => LET f[c \in ChameneosID] == chameneoses[c][2]
                             IN Sum(f, ChameneosID) = 2 * N
THEOREM Spec => []SumMet

====