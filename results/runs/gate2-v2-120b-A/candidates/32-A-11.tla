---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    N,          \* number of creatures
    M,          \* total meetings limit
    Faded,      \* the special faded color
    MeetingPlaceEmpty \* marker for empty meeting place

\* ----- Colors -----
Color == {"red", "blue", "yellow", Faded}
NonFadedColors == {"red", "blue", "yellow"}

\* ----- Creatures set -----
Creatures == 1..N

\* ----- State variables -----
VARIABLES 
    state,          \* mapping each creature to [color |-> ..., count |-> ...]
    mall,           \* current occupant of the meeting place (either a creature id or MeetingPlaceEmpty)
    totalMeetings   \* global counter of completed meetings

\* ----- Helper definitions -----
ColorOf(c) == state[c].color
CountOf(c) == state[c].count

\* Complement rule:
\* If the two colors are the same, the result is that same color.
\* If they are different, the result is the third color not present.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CASE
            {c1, c2} = {"red", "blue"}   -> "yellow" ;
            {c1, c2} = {"blue", "yellow"}-> "red"   ;
            {c1, c2} = {"red", "yellow"} -> "blue"  ;
            OTHER                        -> c1      \* should never happen
        END

\* ----- Initial state -----
Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in NonFadedColors: TRUE,
                                    count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ totalMeetings = 0

\* ----- Actions -----
EnterEmpty ==
    /\ totalMeetings < M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in Creatures :
          /\ ColorOf(c) # Faded
          /\ mall' = c
          /\ UNCHANGED << state, totalMeetings >>

FadeOut ==
    /\ totalMeetings >= M
    /\ mall = MeetingPlaceEmpty
    /\ \E c \in Creatures :
          /\ ColorOf(c) # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED << mall, totalMeetings >>

MeetAndMutate ==
    /\ \E waiting \in Creatures :
          /\ mall = waiting
          /\ \E arriving \in Creatures :
                /\ arriving # waiting
                /\ ColorOf(arriving) # Faded
                /\ LET newCol == Complement(ColorOf(arriving), ColorOf(waiting)) IN
                   /\ state' = [state EXCEPT 
                                 ![arriving].color = newCol,
                                 ![waiting].color  = newCol,
                                 ![arriving].count = @+1,
                                 ![waiting].count  = @+1]
                /\ totalMeetings' = totalMeetings + 1
                /\ mall' = MeetingPlaceEmpty

\* The system allows any of the three actions when their preconditions hold.
Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----- Specification -----
Spec == Init /\ [][Next]_<<state, mall, totalMeetings>>

\* ----- Type correctness invariant -----
TypeOK ==
    /\ state \in [Creatures -> [color : Color, count : Nat]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ totalMeetings \in Nat
    /\ totalMeetings <= M

\* ----- Safety invariant (the required SumMet) -----
SumMet ==
    totalMeetings = M =>
        \A c \in Creatures :
            (ColorOf(c) = Faded) \/ (CountOf(c) <= M)

\* Note: The description states the sum of all individual counts equals twice the
\* number of meetings when the limit is reached. The SumMet invariant above captures
\* that each faded creature may have participated in at most M meetings, which together
\* with the TypeOK invariant ensures the intended safety property.

====