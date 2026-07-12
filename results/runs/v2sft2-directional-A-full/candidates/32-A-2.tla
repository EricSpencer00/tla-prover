---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
ColorSet == {"blue", "red", "yellow", Faded}
Creatures == 1 .. N

\* ----------------------------------------------------------------------
\* Helper for the complement rule
\* ----------------------------------------------------------------------
Complement(a, b) ==
    IF a = b THEN a
    ELSE
        IF a # "blue" /\ b # "blue" THEN "blue"
        ELSE IF a # "red" /\ b # "red" THEN "red"
        ELSE "yellow"

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES CreaturesInfo, MeetingPlace, TotalMeetings

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ CreaturesInfo = [c \in Creatures |-> [color |-> a, meetCnt |-> 0] |
                        a \in {"blue", "red", "yellow"}]
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings < M
    /\ \E c \in Creatures :
        /\ CreaturesInfo[c].color # Faded
        /\ MeetingPlace' = c
        /\ UNCHANGED <<CreaturesInfo, TotalMeetings>>

FadeOut ==
    /\ MeetingPlace = MeetingPlaceEmpty
    /\ TotalMeetings >= M
    /\ \E c \in Creatures :
        /\ CreaturesInfo[c].color # Faded
        /\ CreaturesInfo' = [CreaturesInfo EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<MeetingPlace, TotalMeetings>>

MeetAndMutate ==
    /\ MeetingPlace # MeetingPlaceEmpty
    /\ \E c \in Creatures :
        /\ c # MeetingPlace
        /\ MeetingPlace' = MeetingPlaceEmpty
        /\ CreaturesInfo' = [CreaturesInfo EXCEPT ![MeetingPlace].color = Complement(CreaturesInfo[MeetingPlace].color, CreaturesInfo[c].color),
                                ![c].color = Complement(CreaturesInfo[MeetingPlace].color, CreaturesInfo[c].color),
                                ![MeetingPlace].meetCnt = CreaturesInfo[MeetingPlace].meetCnt + 1,
                                ![c].meetCnt = CreaturesInfo[c].meetCnt + 1]
        /\ TotalMeetings' = TotalMeetings + 1
        /\ UNCHANGED <<MeetingPlace>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<CreaturesInfo, MeetingPlace, TotalMeetings>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ CreaturesInfo \in [Creatures -> [color : ColorSet, meetCnt : Nat]]
    /\ MeetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ TotalMeetings \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual meeting counts equals twice the global counter
\* ----------------------------------------------------------------------
SumMet ==
    /\ TotalMeetings <= M
    /\ TotalMeetings * 2 = \sum c \in Creatures : CreaturesInfo[c].meetCnt

\* ----------------------------------------------------------------------
\* The module must expose the identifiers required by the .cfg
\* ----------------------------------------------------------------------
\* CONSTANTS: N, M, Faded, MeetingPlaceEmpty
\* SPECIFICATION: Spec
\* INVARIANTS: TypeOK, SumMet

====