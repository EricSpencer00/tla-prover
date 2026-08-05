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

VARIABLES chameneoses, meetingPlace, numMeetings

vars == <<chameneoses, meetingPlace, numMeetings>>

ChameneosID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosID

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

Init ==
   /\ chameneoses \in [ChameneosID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* A meetingPlace (the 'Mall' in the original paper) keeps track of the creature
\* that is currently waiting to meet another creature.
\* A chameneos enters an empty meeting place; when a second one enters the place
\* the two chameneoses mutate together: both take on a complementary color.
\* Once the meeting tally reaches its ceiling N, no chameneoses enters the
\* empty meeting place any longer and all waiting chameneoses simply fade.
\* The system terminates once all chameneoses are faded (no live creature left
\* to ever enter the meeting place).
\* Thus meetingPlace and numMeetings stay defined through all of termination.
Meet(cid) ==
   /\ meetingPlace = MeetingPlaceEmpty
   /\ IF numMeetings < N
        THEN /\ meetingPlace' = cid
             /\ chameneoses' = chameneoses
             /\ numMeetings' = numMeetings
        ELSE /\ meetingPlace' = MeetingPlaceEmpty
             /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
             /\ numMeetings' = numMeetings
   /\ meetingPlace # MeetingPlaceEmpty
   /\ meetingPlace # cid
   /\ LET newColor == Complement(chameneoses[cid][1], chameneoses[meetingPlace][1])
      IN /\ meetingPlace' = MeetingPlaceEmpty
         /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                          ![meetingPlace] = <<newColor, @[2] + 1>>]
         /\ numMeetings' = numMeetings + 1

\* Repeatedly try to enter meeting place for chameneoses that are not faded.
\* The system terminates once all chameneoses are faded.
Next ==
   /\ numMeetings < N
   /\ \E c \in { x \in ChameneosID : chameneoses[x][1] /= Faded } : Meet(c)

Spec == Init /\ [][Next]_vars

\* Upon termination, the sum of the (individual) meetings that all creates have
\* been in is equal to 2*N.  It is *not* guaranteed that all chameneoses have
\* been in a meeting with another chameneoses.  See section A. Game termination
\* on page 5 of the original paper.
SumMet ==
   numMeetings = N
      => LET f[c \in ChameneosID] == chameneoses[c][2]
         IN Sum(f, ChameneosID) = 2 * N

THEOREM Spec => []SumMet
====