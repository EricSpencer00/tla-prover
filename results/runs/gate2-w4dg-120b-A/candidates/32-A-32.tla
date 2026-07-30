---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME M \in Nat /\ M > 0

Creatures == 1..N

Colors == {"blue", "red", "yellow", Faded}

Complement(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE LET s == {c1, c2} IN CHOOSE c \in Colors :
    /\ c \notin s
    /\ c # Faded

RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumFn(f, S \ {x})

VARIABLES colCount, meetingPlace, totalMeetings

vars == <<colCount, meetingPlace, totalMeetings>>

TypeOK ==
  /\ colCount \in [Creatures -> [color: Colors, count: 0..(2 * M)]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ colCount \in [Creatures -> [color: {"blue", "red", "yellow"}, count: 0]]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ colCount[c].color # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<colCount, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ colCount[c].color # Faded
  /\ colCount' = [colCount EXCEPT ![c].color = Faded]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ colCount[c].color # Faded
  /\ meetingPlace # MeetingPlaceEmpty
  /\ colCount[meetingPlace].color # Faded
  /\ LET nc1 == Complement(colCount[c].color, colCount[meetingPlace].color) IN
       colCount' = [colCount EXCEPT ![c] = [color |-> nc1, count |-> colCount[c].count + 1],
                                   ![meetingPlace] = [color |-> nc1, count |-> colCount[meetingPlace].count + 1]]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterPlace(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == (totalMeetings = M) => (SumFn([c \in Creatures |-> colCount[c].count], Creatures) = 2 * M)

====