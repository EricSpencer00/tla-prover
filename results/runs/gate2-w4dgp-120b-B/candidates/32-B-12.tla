---- MODULE Chameneos ----
EXTENDS Integers

\* Chameneoses (plural of chameneos; they meet in a mall and take on each other's
\* colors, fading once the meeting limit is reached) should never be left with
\* undefined values: TLC flagged unassigned meetingPlace/numMeetings in a
\* terminal state where nothing is left to do.
\* The fix is to make every Next transition assign *all* the model's variables,
\* so even the terminal "nothing left to meet" action is a complete, well-defined
\* next-state relation over the whole state record.
\* This retains the original semantics (a transition is still either an entry or
\* an exit of the meeting place, or a no-op once the meeting place is full and
\* no creature can meet) while satisfying TLC's requirement of a fully
\* specified successor state.

RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
                       ELSE LET x == CHOOSE x \in S : TRUE
                            IN  f[x] + Sum(f, S \ {x})

Color == {"blue", "red", "yellow"}
Faded == CHOOSE c : c \notin Color
Complement(c1, c2) ==
   IF c1 = c2 THEN c1
              ELSE CHOOSE cid \in Color \ {c1, c2} : TRUE

\* N - total meetings after which chameneoses fade
\* M - number of chameneoses
CONSTANT N, M
ASSUME N \in (Nat \ {0}) /\ M \in (Nat \ {0})
ChameneosesID == 1 .. M
MeetingPlaceEmpty == CHOOSE e : e \notin ChameneosesID

vars == <<chameneoses, meetingPlace, numMeetings>>

TypeOK ==
   /\ chameneoses \in [ ChameneosesID -> (Color \cup {Faded}) \X (0 .. N) ]
   /\ meetingPlace \in ChameneosesID \cup {MeetingPlaceEmpty}
   /\ numMeetings \in 0 .. N

Init ==
   /\ chameneoses \in [ChameneosesID -> Color \X {0}]
   /\ meetingPlace = MeetingPlaceEmpty
   /\ numMeetings = 0

\* Meeting place is empty: a non-faded creature enters it, or fades out if the
\* meeting limit is reached.  Meeting place is occupied: the waiting creature
\* and the new arrival color each other and both count the meeting.
Meet(cid) ==
   IF meetingPlace = MeetingPlaceEmpty
   THEN IF numMeetings < N
        THEN /\ meetingPlace' = cid
             /\ UNCHANGED <<chameneoses, numMeetings>>
        ELSE /\ chameneoses' = [chameneoses EXCEPT ![cid] = <<Faded, @[2]>>]
             /\ UNCHANGED <<meetingPlace, numMeetings>>
   ELSE /\ meetingPlace # cid
        /\ meetingPlace' = MeetingPlaceEmpty
        /\ chameneoses' =
            LET newColor == Complement(chameneoses[cid][1], chameneoses[meetingPlace][1])
            IN [chameneoses EXCEPT ![cid] = <<newColor, @[2] + 1>>,
                                      ![meetingPlace] = <<newColor, @[2] + 1>>]
        /\ numMeetings' = numMeetings + 1

\* When nothing can enter the meeting place (all are faded or the place is
\* full and the meeting limit is reached), stay put but still assign every
\* state variable.
Stall ==
   /\ meetingPlace # MeetingPlaceEmpty => numMeetings = N
   /\ chameneoses[meetingPlace][1] = Faded
   /\ UNCHANGED vars

Next == /\ \E c \in { x \in ChameneosesID : chameneoses[x][1] /= Faded } : Meet(c)
        \/ Stall

Spec == Init /\ [][Next]_vars

\* Sum of individual meeting counts equals twice the meeting limit once the
\* game has terminated: each meeting advances two creatures in lockstep.
SumMet == numMeetings = N => LET f[c \in ChameneosesID] == chameneoses[c][2]
                             IN Sum(f, ChameneosesID) = 2 * N
THEOREM Spec => []SumMet

====