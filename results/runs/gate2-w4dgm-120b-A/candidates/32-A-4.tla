---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Extinction-level: the meeting place capacity, not the creature population.
\* A meeting takes two participants and increments their own counts as well as the global one,
\* which is why the global count being double the number of meetings is a real safety statement.
\* One creature is never forced to meet; it can simply miss out and end up nowhere near that bound.
Creatures == 1..N
Colors == {"blue","red","yellow",Faded}
SumOfMeetingCounts == (M * (M + 1)) \div 2

VARIABLES cstate, meetingPlace, globalCount

vars == <<cstate, meetingPlace, globalCount>>

\* A creature's color and its personal meeting count travel together as a pair.
CurrentColors == { cstate[i][1] : i \in Creatures }

TypeOK ==
  /\ cstate \in [Creatures -> (Colors \X (0..M))]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ globalCount \in 0..M

\* Each meeting pulls two participants out of the global pool together.
MeetingCountSumMatchesGlobal ==
  globalCount = M => SumOfMeetingCounts = (cstate[1][2] + cstate[2][2]
                                          + cstate[3][2] + cstate[4][2])

Init ==
  /\ cstate \in [Creatures -> ({"blue","red","yellow"} \X {0})]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ globalCount = 0

\* Creatures are free to drift into the meeting place whenever it is open.
EnterMeetingPlace(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ globalCount < M
  /\ cstate[c][1] # Faded
  /\ meetingPlace' = c
  /\ UNCHANGED <<cstate, globalCount>>

FadeOut(c) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ globalCount = M
  /\ cstate[c][1] # Faded
  /\ cstate' = [cstate EXCEPT ![c] = <<Faded, cstate[c][2]>>]
  /\ UNCHANGED <<meetingPlace, globalCount>>

\* Complementing takes both in the same direction, so the meeting is irreversible.
MeetAndMutate(c) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # c
  /\ cstate[c][1] # Faded
  /\ cstate[meetingPlace][1] # Faded
  /\ LET newcol == IF cstate[c][1] = cstate[meetingPlace][1]
                 THEN cstate[c][1]
                 ELSE CHOOSE x \in {"blue","red","yellow"} :
                          (x # cstate[c][1]) /\ (x # cstate[meetingPlace][1])
     IN cstate' = [cstate EXCEPT ![c] = <<newcol, cstate[c][2] + 1>>,
                                ![meetingPlace] = <<newcol, cstate[meetingPlace][2] + 1>>]
  /\ meetingPlace' = MeetingPlaceEmpty
  /\ globalCount' = globalCount + 1

Next ==
  \/ \E c \in Creatures : EnterMeetingPlace(c) \/ FadeOut(c) \/ MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

====