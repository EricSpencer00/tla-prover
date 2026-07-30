---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* A creature's state: its current color together with the number of meetings
\* it has participated in so far.
CreatureState == [color: {"blue", "red", "yellow", Faded}, met: 0..M]

ASSUME M \in Nat /\ N \in Nat

VARIABLES creatures, meetingPlace, totalMeetings

vars == <<creatures, meetingPlace, totalMeetings>>

TypeOK ==
    /\ creatures \in [1..N -> CreatureState]
    /\ meetingPlace \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in 0..M

RECURSIVE SumMetOver(_)
SumMetOver(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE e \in S : TRUE IN creatures[x].met + SumMetOver(S \ {x})

\* Each meeting touches exactly two participants; once the meeting place is
\* closed this arithmetic is what the safety property is checking against.
SumMet == SumMetOver(1..N)

Init ==
    /\ creatures \in [1..N -> CreatureState]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {"blue", "red"} THEN "yellow"
    ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
    ELSE IF {c1, c2} = {"red", "yellow"} THEN "blue"
    ELSE Faded

EnterMeetingPlace(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ creatures[c].color # Faded
    /\ totalMeetings < M
    /\ meetingPlace' = c
    /\ UNCHANGED <<creatures, totalMeetings>>

FadeOut(c) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = M
    /\ creatures[c].color # Faded
    /\ creatures' = [creatures EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<meetingPlace, totalMeetings>>

\* The arriving creature and the waiting creature both adopt the same
\* post-meeting color, so both coordinated outcomes are recorded identically.
MeetAndMutate(c) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ creatures[c].color # Faded
    /\ LET other == meetingPlace
           newcol == Complement(creatures[c].color, creatures[other].color)
       IN /\ creatures' = [creatures EXCEPT ![c].color = newcol, ![c].met = @ + 1,
                                          ![other].color = newcol, ![other].met = @ + 1]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E c \in 1..N : EnterMeetingPlace(c)
    \/ \E c \in 1..N : FadeOut(c)
    \/ \E c \in 1..N : MeetAndMutate(c)

Spec == Init /\ [][Next]_vars

SumMetMatches ==
    totalMeetings = M => SumMet = 2 * M

====