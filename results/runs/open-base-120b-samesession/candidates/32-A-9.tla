---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    N,               \* number of creatures
    M,               \* total meetings limit
    Faded,           \* the faded color
    MeetingPlaceEmpty

\* Primary colors
CONSTANTS Blue, Red, Yellow

\* Sets of colors
PrimaryColors == {Blue, Red, Yellow}
Colors == PrimaryColors \cup {Faded}

\* State variables
VARIABLES 
    creatures,   \* [1..N -> (Colors \X Nat)]  each <<color, meetingCount>>
    mall,        \* either MeetingPlaceEmpty or a creature id
    total        \* total number of meetings performed

\* ----------------------------------------------------------------------
\* Complement rule
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE IF {c1, c2} = {Blue, Red} THEN
        Yellow
    ELSE IF {c1, c2} = {Red, Yellow} THEN
        Blue
    ELSE IF {c1, c2} = {Blue, Yellow} THEN
        Red
    ELSE
        Faded   \* should never happen for non‑faded inputs

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ \A i \in 1..N : \E c \in PrimaryColors : creatures[i] = <<c, 0>>
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions

EnterEmpty ==
    \E i \in 1..N :
        /\ mall = MeetingPlaceEmpty
        /\ total < M
        /\ creatures[i][1] # Faded
        /\ mall' = i
        /\ UNCHANGED <<creatures, total>>

FadeOut ==
    \E i \in 1..N :
        /\ mall = MeetingPlaceEmpty
        /\ total = M
        /\ creatures[i][1] # Faded
        /\ creatures' = [creatures EXCEPT ![i] = <<Faded, creatures[i][2]>>]
        /\ mall' = MeetingPlaceEmpty
        /\ UNCHANGED total

MeetAndMutate ==
    \E i \in 1..N, j \in 1..N :
        /\ mall = j
        /\ i # j
        /\ total < M
        /\ creatures[i][1] # Faded
        /\ creatures[j][1] # Faded
        LET newc == Complement(creatures[i][1], creatures[j][1]) IN
        /\ creatures' = [k \in 1..N |-> 
                IF k = i \/ k = j 
                THEN <<newc, creatures[k][2] + 1>>
                ELSE creatures[k]]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total + 1

Next == 
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<creatures, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ creatures \in [1..N -> (Colors \X Nat)]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

SumMet ==
    (total = M) => (Sum({i \in 1..N}, creatures[i][2]) = 2 * M)

====