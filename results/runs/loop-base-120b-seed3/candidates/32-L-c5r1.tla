---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* Bounds for individual meeting counts
\* ----------------------------------------------------------------------
CountRange == 0..M

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES creatures, mall, total

\* ----------------------------------------------------------------------
\* Complement rule
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE IF (c1 = "blue" /\ c2 = "red") \/ (c1 = "red" /\ c2 = "blue") THEN
        "yellow"
    ELSE IF (c1 = "blue" /\ c2 = "yellow") \/ (c1 = "yellow" /\ c2 = "blue") THEN
        "red"
    ELSE
        "blue" \* the remaining case: red & yellow

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ creatures \in [1..N -> [color : NonFadedColors, count : CountRange]]
    /\ \A c \in 1..N: creatures[c].count = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in 1..N :
        /\ creatures[c].color # Faded
        /\ mall' = c
        /\ UNCHANGED << creatures, total >>

Fade ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E c \in 1..N :
        /\ creatures[c].color # Faded
        /\ creatures' = [creatures EXCEPT ![c].color = Faded]
        /\ UNCHANGED << mall, total >>

Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E c2 \in 1..N :
        LET c1 == mall IN
        /\ c2 # c1
        /\ creatures[c1].color # Faded
        /\ creatures[c2].color # Faded
        LET newcol == Complement(creatures[c1].color, creatures[c2].color) IN
            /\ creatures' = [creatures EXCEPT
                               ![c1] = [color |-> newcol,
                                        count |-> creatures[c1].count + 1],
                               ![c2] = [color |-> newcol,
                                        count |-> creatures[c2].count + 1]]
            /\ mall' = MeetingPlaceEmpty
            /\ total' = total + 1
        /\ UNCHANGED << >>

Next ==
    \/ Enter
    \/ Fade
    \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<creatures, mall, total>>

\* ----------------------------------------------------------------------
\* Recursive function to sum meeting counts
\* ----------------------------------------------------------------------
RECURSIVE Count(_)
Count(i) ==
    IF i = 0 THEN 0
    ELSE Count(i-1) + creatures[i].count

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ creatures \in [1..N -> [color : Colors, count : CountRange]]
    /\ mall \in (MeetingPlaceEmpty \cup 1..N)
    /\ total \in Nat

SumMet ==
    (total = M) => (Count(N) = 2 * M)

====