---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the special color indicating a faded creature
    MeetingPlaceEmpty \* sentinel value for an empty meeting place

\* ----------------------------------------------------------------------
\* Colors
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* Helper definitions
ThirdColor(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CHOOSE c \in NonFadedColors : c # c1 /\ c # c2

Comp(c1, c2) ==
    IF c1 = c2 THEN c1 ELSE ThirdColor(c1, c2)

\* ----------------------------------------------------------------------
\* Variables
VARIABLES 
    colors,          \* [creature -> color]
    counts,          \* [creature -> Nat] number of meetings participated in
    meetingPlace,    \* either MeetingPlaceEmpty or a creature identifier
    total            \* total number of completed meetings

\* ----------------------------------------------------------------------
\* Type definitions for readability
Creatures == 1..N

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ colors = [c \in Creatures |-> CHOOSE col \in NonFadedColors : TRUE]
    /\ counts = [c \in Creatures |-> 0]
    /\ meetingPlace = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
EnterEmpty ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
          /\ colors[c] # Faded
          /\ meetingPlace' = c
          /\ colors' = colors
          /\ counts' = counts
          /\ total' = total

FadeOut ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ total >= M
    /\ \E c \in Creatures :
          /\ colors[c] # Faded
          /\ meetingPlace' = MeetingPlaceEmpty
          /\ colors' = [colors EXCEPT ![c] = Faded]
          /\ counts' = counts
          /\ total' = total

MeetAndMutate ==
    /\ meetingPlace # MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
          /\ c # meetingPlace
          /\ colors[c] # Faded
          /\ LET w == meetingPlace IN
             /\ colors' = [colors EXCEPT 
                            ![c] = Comp(colors[c], colors[w]),
                            ![w] = Comp(colors[c], colors[w])]
             /\ counts' = [counts EXCEPT 
                            ![c] = counts[c] + 1,
                            ![w] = counts[w] + 1]
             /\ meetingPlace' = MeetingPlaceEmpty
             /\ total' = total + 1

\* ----------------------------------------------------------------------
\* Stuttering step to avoid deadlock when everything is faded and no further
\* progress is possible.
Stutter ==
    /\ meetingPlace = MeetingPlaceEmpty
    /\ total >= M
    /\ \A c \in Creatures : colors[c] = Faded
    /\ UNCHANGED <<colors, counts, meetingPlace, total>>

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate
    \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<colors, counts, meetingPlace, total>>

\* ----------------------------------------------------------------------
\* Safety invariant: type correctness
TypeOK ==
    /\ colors \in [Creatures -> Colors]
    /\ counts \in [Creatures -> Nat]
    /\ meetingPlace \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual meeting counts equals twice the total
SumMet ==
    /\ total = M => 
          \A c \in Creatures : colors[c] = Faded
    /\ Sum(counts) = 2 * total

\* ----------------------------------------------------------------------
\* Theorems (optional, not required by the .cfg but harmless)
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====