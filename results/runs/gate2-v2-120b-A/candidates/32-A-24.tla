---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be bound in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    N,               \* number_of_creatures, a positive natural number
    M,               \* total_meetings_limit, a positive natural number
    Faded,           \* a distinguished value representing the faded color
    MeetingPlaceEmpty \* a distinguished value representing an empty meeting place

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Creatures == 1..N
Colors    == {"blue", "red", "yellow", Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    state,          \* [creature -> [color : Colors, count : Nat]]
    meetingPlace,   \* either MeetingPlaceEmpty or a creature identifier
    totalMeetings   \* Nat, the global counter of completed meetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ColorOf(c) == state[c].color
CountOf(c) == state[c].count

\* The complement rule:
\*   - If the two colors are the same, the result is that same color.
\*   - If they are different, the result is the third color (the one that is
\*     neither of the two).
Complement(x, y) ==
    IF x = y THEN x
    ELSE IF {x, y} = {"blue", "red"} THEN "yellow"
    ELSE IF {x, y} = {"blue", "yellow"} THEN "red"
    ELSE IF {x, y} = {"red", "yellow"} THEN "blue"
    ELSE Faded \* should never happen

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings = 0
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue", "red", "yellow"}: TRUE,
                                   count |-> 0]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(c) ==
    /\ c \in Creatures
    /\ state[c].color # Faded
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings < M
    /\ meetingPlace' = c
    /\ UNCHANGED << state, totalMeetings >>

Fade(c) ==
    /\ c \in Creatures
    /\ state[c].color # Faded
    /\ meetingPlace = MeetingPlaceEmpty
    /\ totalMeetings >= M
    /\ state' = [state EXCEPT ![c].color = Faded]
    /\ UNCHANGED << meetingPlace, totalMeetings >>

MeetAndMutate(c) ==
    /\ c \in Creatures
    /\ state[c].color # Faded
    /\ meetingPlace # MeetingPlaceEmpty
    /\ meetingPlace # c
    /\ LET d == meetingPlace IN
       /\ state[d].color # Faded
       /\ LET newColor == Complement(state[c].color, state[d].color) IN
          /\ state' = [state EXCEPT
                        ![c].color = newColor,
                        ![c].count = @ + 1,
                        ![d].color = newColor,
                        ![d].count = @ + 1]
    /\ meetingPlace' = MeetingPlaceEmpty
    /\ totalMeetings' = totalMeetings + 1

\* All possible steps
Next ==
    \/ \E c \in Creatures: Enter(c)
    \/ \E c \in Creatures: Fade(c)
    \/ \E c \in Creatures: MeetAndMutate(c)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, meetingPlace, totalMeetings>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [Creatures -> [color : Colors, count : Nat]]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual counts equals twice the total meetings
\* after the limit has been reached (and always, because the equality holds
\* after each meeting and initial state satisfies it with both sides zero).
\* ----------------------------------------------------------------------
SumMet ==
    \A c \in Creatures: state[c].count \in Nat
    /\ (totalMeetings >= M => 
        Sum({state[c].count : c \in Creatures}) = 2 * totalMeetings)

\* ----------------------------------------------------------------------
\* Theorem (optional, to help TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []SumMet

====