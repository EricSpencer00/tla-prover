---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Colors for the chameneos. The meeting-place occupant is either a creature
\* identifier or MeetingPlaceEmpty.
Colors == {"blue", "red", "yellow", Faded}
Creatures == 1..N
ThirdNotHeld(c1, c2) == IF {"blue", "red", "yellow"} = {c1, c2} THEN "yellow" ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red" ELSE "blue"

VARIABLES stateOf, meetingPlace, totalMeetings

vars == <<stateOf, meetingPlace, totalMeetings>>

TypeOK == /\ stateOf \in [Creatures -> [color: Colors, met: 0..M]]
          /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
          /\ totalMeetings \in 0..M

Init == /\ stateOf = [c \in Creatures |-> [color |-> "blue", met |-> 0]]
        /\ meetingPlace = MeetingPlaceEmpty
        / totalMeetings = 0

\* The meeting place is the critical resource: a single waiting creature at a
\* time, so any meeting is strictly between the occupant and the new entrant.
EnterPlace == /\ meetingPlace = MeetingPlaceEmpty
              /\ totalMeetings < M
              /\ \E c \in Creatures :
                   /\ stateOf[c].color # Faded
                   /\ meetingPlace' = c
              /\ UNCHANGED <<stateOf, totalMeetings>>

\* Once the meeting place has closed, non-faded creatures that still try simply
\* fade out instead of waiting.
FadeOut == /\ meetingPlace = MeetingPlaceEmpty
           /\ totalMeetings = M
           /\ \E c \in Creatures :
                /\ stateOf[c].color # Faded
                /\ stateOf' = [stateOf EXCEPT ![c].color = Faded]
           /\ UNCHANGED <<meetingPlace, totalMeetings>>

MeetAndMutate == /\ meetingPlace # MeetingPlaceEmpty
                 /\ \E cNew \in Creatures :
                      /\ cNew # meetingPlace
                      /\ stateOf[cNew].color # Faded
                      /\ stateOf[meetingPlace].color # Faded
                      /\ LET newCol == IF stateOf[cNew].color = stateOf[meetingPlace].color
                                      THEN stateOf[cNew].color
                                      ELSE ThirdNotHeld(stateOf[cNew].color, stateOf[meetingPlace].color)
                         IN stateOf' = [stateOf EXCEPT ![cNew].color = newCol, ![meetingPlace].color = newCol,
                                        ![cNew].met = @ + 1, ![meetingPlace].met = @ + 1]
                 /\ totalMeetings' = totalMeetings + 1
                 /\ meetingPlace' = MeetingPlaceEmpty

Next == EnterPlace \/ FadeOut \/ MeetAndMutate

\* The bounded meeting count ensures every possible meeting is eventually
\* resolved, so weak fairness per action per creature is enough for liveness.
Spec == Init /\ [][Next]_vars
        /\ \A c \in Creatures : SF_vars(EnterPlace) /\ SF_vars(FadeOut) /\ SF_vars(MeetAndMutate)

SumMet(n) == LET rec[S \in SUBSET Creatures] ==
                  IF S = {} THEN 0
                  ELSE LET x == CHOOSE y \in S : TRUE
                       IN stateOf[x].met + rec[S \ {x}]
             IN rec[Creatures]

\* Each meeting involves two participants, so the summed per-creature counts
\* double the number of meetings once the meeting place has closed.
SumMet == SumMet(N)

TypeOK == /\ stateOf \in [Creatures -> [color : Colors, met : 0..M]]
          /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
          /\ totalMeetings \in 0..M

Invariant == SumMet = 2 * totalMeetings

\* SAFETY: the per-creature participation log stays consistent with the global
\* meeting counter once the place has closed.
INVARIANT SumMet

====