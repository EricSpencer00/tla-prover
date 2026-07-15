---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,              \* number of creatures
    M,              \* total meetings limit
    Faded,          \* the special faded color
    MeetingPlaceEmpty \* sentinel value for empty meeting place

\* ----- Types -----
Colors == {"blue", "red", "yellow", Faded}
CreatureIds == 1..N

\* ----- State Variables -----
VARIABLES
    state,          \* mapping CreatureId -> [color : Colors, count : Nat]
    meetingPlace,   \* either MeetingPlaceEmpty or a CreatureId
    totalMeetings   \* Nat counting total completed meetings

\* ----- Helper definitions -----
ColorOf(cre) == state[cre].color
CountOf(cre) == state[cre].count

\* Complement rule: given two colors, return the resulting color for both
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CASE c1 = "blue"  /\ c2 = "red"    -> "yellow" []
        []  c1 = "red"   /\ c2 = "blue"   -> "yellow" []
        []  c1 = "blue"  /\ c2 = "yellow" -> "red"    []
        []  c1 = "yellow"/\ c2 = "blue"   -> "red"    []
        []  c1 = "red"   /\ c2 = "yellow" -> "blue"   []
        []  c1 = "yellow"/\ c2 = "red"    -> "blue"   []
        []  OTHER -> Faded \* should never happen for non‑faded inputs

\* ----- Initial state -----
Init ==
    /\ state = [c \in CreatureIds |-> [color |-> CHOOSE col \in {"blue","red","yellow"} : TRUE,
                                      count |-> 0]]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* ----- Actions -----
Enter(cre) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ state[cre].color # Faded
    /\ meetingPlace' = cre
    /\ UNCHANGED << state, totalMeetings >>

Fade(cre) ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ state[cre].color # Faded
    /\ state' = [state EXCEPT ![cre].color = Faded]
    /\ UNCHANGED << meetingPlace, totalMeetings >>

MeetAndMutate(cre) ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # cre
    /\ state[cre].color # Faded
    /\ state[meetingPlace].color # Faded
    /\ let waiting == meetingPlace in
       /\ newCol == Complement(state[cre].color, state[waiting].color)
       /\ state' = [state EXCEPT
                    ![cre].color = newCol,
                    ![waiting].color = newCol,
                    ![cre].count = @ + 1,
                    ![waiting].count = @ + 1]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

Next ==
    \/ \E cre \in CreatureIds: Enter(cre)
    \/ \E cre \in CreatureIds: Fade(cre)
    \/ \E cre \in CreatureIds: MeetAndMutate(cre)

\* ----- Specification -----
Spec == Init /\ [][Next]_<<state, meetingPlace, totalMeetings>>

\* ----- Type correctness invariant -----
TypeOK ==
    /\ state \in [CreatureIds -> [color : Colors, count : Nat]]
    /\ meetingPlace \in MeetingPlaceEmpty \cup CreatureIds
    /\ totalMeetings \in Nat

\* ----- Safety invariant: sum of individual meeting counts equals twice the total meetings -----
SumMet ==
    /\ totalMeetings <= M
    /\ \A cre \in CreatureIds: state[cre].count <= totalMeetings
    /\ (totalMeetings = M) => 
          ( \A cre \in CreatureIds: state[cre].color = Faded )
    /\ ( \Sum cre \in CreatureIds : state[cre].count ) = 2 * totalMeetings

\* The specification name required by the .cfg
SPECIFICATION Spec

\* The invariant names required by the .cfg
INVARIANT TypeOK
INVARIANT SumMet

====