---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

Creatures == 1 .. N
Colors == {"blue", "red", "yellow", Faded}

VARIABLES state, meetingPlace, totalCycles
vars == <<state, meetingPlace, totalCycles>>

ThirdColor(c1, c2) ==
  IF c1 = c2 THEN c1
  ELSE (CHOOSE c \in {"blue", "red", "yellow"} : c # c1 /\ c # c2)

TotalParticipations ==
  LET add[S \in SUBSET Creatures] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE IN state[x][2] + add[S \ {x}]
  IN add[Creatures]

TypeOK ==
  /\ state \in [Creatures -> Colors \X Nat]
  /\ meetingPlace \in {MeetingPlaceEmpty} \cup Creatures
  /\ totalCycles \in Nat

Init ==
  /\ state \in [Creatures -> (Colors \ {Faded}) \X {0}]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalCycles = 0

EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalCycles < M
  /\ state[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<state, totalCycles>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalCycles >= M
  /\ state[c][1] # Faded
  /\ state' = [state EXCEPT ![c] = <<Faded, @2>>]
  /\ UNCHANGED <<meetingPlace, totalCycles>>

MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ totalCycles < M
  /\ state[c][1] # Faded
  /\ state[meetingPlace][1] # Faded
  /\ LET nc == ThirdColor(state[c][1], state[meetingPlace][1]) IN
       state' = [state EXCEPT ![c] = <<nc, @2 + 1>, ![meetingPlace] = <<nc, @2 + 1>>]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ totalCycles' = totalCycles + 1

Next ==
  \/ \E c \in Creatures : EnterMeetingPlace(c)
  \/ \E c \in Creatures : FadeOut(c)
  \/ \E c \in Creatures : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMet == (totalCycles = M) => (TotalParticipations = 2 * M)
====