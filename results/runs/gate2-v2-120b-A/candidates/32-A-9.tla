---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    N,               \* number of creatures (positive natural)
    M,               \* total meetings limit (positive natural)
    Faded,           \* sentinel value for faded color
    MeetingPlaceEmpty \* sentinel value for empty meeting place

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}
CreatureIds == 1 .. N
MeetingPlaceEmptyValue == MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    colors,          \* [creature -> color]
    counts,          \* [creature -> Nat]  number of meetings per creature
    mall,            \* either MeetingPlaceEmpty or a creature id
    totalMeetings    \* Nat, total number of meetings completed

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Other(x) == {y \in CreatureIds : y # x}

\* Complement rule as described:
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in {"blue", "red", "yellow"} : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ colors = [i \in CreatureIds |-> 
        CHOOSE col \in {"blue", "red", "yellow"} : TRUE]
        \* nondeterministically assign each creature a non‑faded color
    /\ counts = [i \in CreatureIds |-> 0]
    /\ mall = MeetingPlaceEmptyValue
    /\ totalMeetings = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ totalMeetings < M
    /\ mall = MeetingPlaceEmptyValue
    /\ \E i \in CreatureIds :
        /\ colors[i] # Faded
        /\ mall' = i
        /\ UNCHANGED << colors, counts, totalMeetings >>

FadeOut ==
    /\ totalMeetings >= M
    /\ mall = MeetingPlaceEmptyValue
    /\ \E i \in CreatureIds :
        /\ colors[i] # Faded
        /\ colors' = [colors EXCEPT ![i] = Faded]
        /\ UNCHANGED << counts, mall, totalMeetings >>

MeetAndMutate ==
    /\ mall # MeetingPlaceEmptyValue
    /\ \E j \in CreatureIds :
        /\ j # mall
        /\ colors[j] # Faded
        /\ \E i \in CreatureIds :
            /\ i # j
            /\ i # mall
            /\ colors[i] # Faded
            /\ LET newCol == Complement(colors[i], colors[j]) IN
               /\ colors' = [colors EXCEPT ![i] = newCol, ![j] = newCol]
            /\ counts' = [counts EXCEPT ![i] = @ + 1, ![j] = @ + 1]
            /\ totalMeetings' = totalMeetings + 1
            /\ mall' = MeetingPlaceEmptyValue
            /\ UNCHANGED << >>

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<colors, counts, mall, totalMeetings>>

\* ----------------------------------------------------------------------
\* Type correctness invariant (optional but useful)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ colors \in [CreatureIds -> Colors]
    /\ counts \in [CreatureIds -> Nat]
    /\ mall \in {MeetingPlaceEmptyValue} \cup CreatureIds
    /\ totalMeetings \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant required by the description
\* ----------------------------------------------------------------------
SumMet ==
    /\ totalMeetings = M
    => 2 * M = \Sum i \in CreatureIds : counts[i]

\* ----------------------------------------------------------------------
\* THEOREMS (to expose the identifiers for the .cfg file)
\* ----------------------------------------------------------------------
THEOREM SpecIsSpec == Spec
THEOREM TypeOKInv == TypeOK
THEOREM SumMetInv == SumMet

====