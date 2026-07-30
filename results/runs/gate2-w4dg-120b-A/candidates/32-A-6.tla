---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

ASSUME N \in Nat /\ N > 0 /\ M \in Nat /\ M > 0

Creatures == 0 .. (N - 1)
Colors == {"blue", "red", "yellow", Faded}

VARIABLES status, meetingPlace, totalMeetings

vars == <<status, meetingPlace, totalMeetings>>

MyColorOf(c) == (status[c]).1
MetCountOf(c) == (status[c]).2

RunningCreatures == {c \in Creatures : MyColorOf(c) # Faded}

RECURSIVE SumMet(_)
SumMet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN MetCountOf(x) + SumMet(S \ {x})

Complement(c1, c2) ==
  IF MyColorOf(c1) = MyColorOf(c2) THEN MyColorOf(c1)
  ELSE LET s == {MyColorOf(c1), MyColorOf(c2)} IN
         CHOOSE col \in Colors \ s : col

Blank == "blank"

InitStatus(c) == CHOOSE col \in {"blue", "red", "yellow"} : [1 |-> col, 2 |-> 0]

TypeOK ==
  /\ status \in [Creatures -> [1..2 -> Colors]]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ status = [c \in Creatures |-> InitStatus(c)]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

EnterWaiting(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ MyColorOf(c) # Faded
  /\ totalMeetings < M
  /\ meetingPlace' = c
  /\ UNCHANGED <<status, totalMeetings>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ MyColorOf(c) # Faded
  /\ totalMeetings = M
  /\ status' = [status EXCEPT ![c] = [status[c][1] |-> Faded, status[c][2] |-> status[c][2]]]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ MyColorOf(c) # Faded
  /\ MyColorOf(meetingPlace) # Faded
  /\ LET newcol == Complement(c, meetingPlace) IN
       status' = [status EXCEPT ![c] = [status[c][1] |-> newcol, status[c][2] |-> status[c][2] + 1],
                            ![meetingPlace] = [status[meetingPlace][1] |-> newcol, status[meetingPlace][2] |-> status[meetingPlace][2] + 1]]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E c \in Creatures : EnterWaiting(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

MeetingCountMatches ==
  (totalMeetings = M) => (SumMet(Creatures) = 2 * M)

====