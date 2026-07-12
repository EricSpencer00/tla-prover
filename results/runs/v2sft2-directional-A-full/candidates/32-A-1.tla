---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Types and constants
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors == {"blue", "red", "yellow", Faded}
\* The set of normal colors used for complement computation
NormalColors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* Helpers
\* ----------------------------------------------------------------------
ComplementRule(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE NormalColors \ {c1, c2}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, meetingPlace, globalMeetings

\* ----------------------------------------------------------------------
\* Type correctness variables
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [Creatures -> [color : Colors, meetings : Nat]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ globalMeetings \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE(color \in NormalColors: TRUE), meetings |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ globalMeetings = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ globalMeetings < M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ meetingPlace' = c
          /\ UNCHANGED <<state, globalMeetings>>

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ globalMeetings >= M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<meetingPlace, globalMeetings>>

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ globalMeetings < M
    /\ \E c \in Creatures :
          /\ meetingPlace # c
          /\ c' = c
          /\ state' = [state EXCEPT
                ![c].color = ComplementRule(state[meetingPlace].color, state[c].color),
                ![c].meetings = state[c].meetings + 1,
                ![meetingPlace].color = ComplementRule(state[meetingPlace].color, state[c].color),
                ![meetingPlace].meetings = state[meetingPlace].meetings + 1]
          /\ meetingPlace' = MeetingPlaceEmpty
          /\ globalMeetings' = globalMeetings + 1

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

Spec ==
    Init /\ [][Next]_<<state, meetingPlace, globalMeetings>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
SumMet ==
    /\ globalMeetings >= M
    /\ \E c \in Creatures : state[c].color = Faded
    /\ \E c \in Creatures : state[c].color # Faded
    /\ \E c \in Creatures : state[c].meetings = 0
    /\ \E c \in Creatures : state[c].meetings = 0
    /\ \E c \in Creatures : state[c].meetings >= 0
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ \E c \in Creatures : state[c].meetings <= M
    /\ globalMeetings = M
    /\ \E c \in Creatures : state[c].meetings = state[c].meetings
    /\ (\E c \in Creatures : state[c].meetings) * 2 = 2 * globalMeetings

\* ----------------------------------------------------------------------
\* SAFETY PROPERTY: When the global meeting counter reaches the limit,
\* the sum of all individual creature meeting counts equals twice the limit.
\* ----------------------------------------------------------------------
SumMeetingsInvariant ==
    /\ globalMeetings = M
    /\ \E sum \in Nat : sum = 2 * globalMeetings
    /\ sum = \Sum c \in Creatures : state[c].meetings

\* ----------------------------------------------------------------------
\* Definition of invariants for TLC
\* ----------------------------------------------------------------------
INVARIANT SumMeetingsInvariant

====