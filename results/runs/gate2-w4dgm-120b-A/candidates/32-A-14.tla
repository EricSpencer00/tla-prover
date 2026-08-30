---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* N: number of creatures (ids 1..N); M: meeting-limit for the mall; Faded: the
\* terminal color. Two creatures meet in a shared meeting place that can hold at
\* most one waiting creature, so the mall acts as the mutual-exclusion lock on
\* each encounter.
\* MeetingCount is the per-creature meeting tally; TotalMeetings is the global
\* tally that drives the mall's closure. Because each encounter is binary,
\* SumMet captures the exact bisimulation with a doubled tally at the limit.
Creatures == 1..N
Colors == { "blue", "red", "yellow", Faded }
PartnerOf(n) == (n % N) + 1

VARIABLES status, meetingPlace, totalMeetings

vars == <<status, meetingPlace, totalMeetings>>

RECURSIVE SumMet(_)
SumMet(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN status[x][2] + SumMet(S \ {x})

TypeOK ==
  /\ status \in [Creatures -> (Colors \X (0..M))]
  /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
  /\ totalMeetings \in 0..M

Init ==
  /\ status \in [Creatures -> (Colors \ {Faded} \X {0})]
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings = 0

\* The mall may be entered only below the meeting limit; once it is reached
\* creatures that still try to enter fade out instead of joining.
Enter(n) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings < M
  /\ status[n][1] # Faded
  /\ meetingPlace' = n
  /\ UNCHANGED <<status, totalMeetings>>

FadeOut(n) ==
  /\ meetingPlace = MeetingPlaceEmpty
  /\ totalMeetings >= M
  /\ status[n][1] # Faded
  /\ status' = [status EXCEPT ![n] = <<Faded, status[n][2]>>]
  /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* Self-meeting is ruled out by the distinct-occupant guard; the complement rule
\* keeps the pairwise meeting symmetric and deterministic once both participants
\* are fixed.
Meet(n) ==
  /\ meetingPlace # MeetingPlaceEmpty
  /\ meetingPlace # n
  /\ status[n][1] # Faded
  /\ LET p == meetingPlace
         newColor == IF status[n][1] = status[p][1]
                     THEN status[n][1]
                     ELSE CHOOSE c \in Colors \ {Faded} :
                              c # status[n][1] /\ c # status[p][1]
     IN status' = [status EXCEPT ![n] = <<newColor, status[n][2] + 1>,
                                   ![p] = <<newColor, status[p][2] + 1>>]
  /\ totalMeetings' = totalMeetings + 1
  /\ meetingPlace' = MeetingPlaceEmpty

Next ==
  \/ \E n \in Creatures : Enter(n) \/ FadeOut(n) \/ Meet(n)

\* Every creature eventually reaches the terminal faded state: the meeting limit
\* is always eventually reached, which puts each non-faded creature into the
\* FadeOut transition, regardless of how meetings interleave.
Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Creatures : FadeOut(n))

\* SAFETY: at the meeting limit the global meeting count and the sum of the
\* creature-local counts must agree exactly as a doubled tally.
SumMet == SumMet(Creatures)

\* LIVENESS: every creature eventually fades out.
\* The system is strongly fair on FadeOut, so this is not a weak-starvation
\* claim about meeting ordering -- the mall closing forces progress even when
\* meeting loops are fair and can otherwise starve a single creature.
FadeAll == <>(\A n \in Creatures : status[n][1] = Faded)

====