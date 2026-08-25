---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    N,               \* Number of creatures
    M,               \* Total meetings limit
    Faded,           \* Color representing a faded creature
    MeetingPlaceEmpty \* Symbol representing an empty meeting place

\* ----------------------------------------------------------------------
\* Colors
Colors == {"blue", "red", "yellow", Faded}
NonFadedColors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    c,      \* Mapping from each creature to a record [col, cnt]
    mall,   \* Occupant of the meeting place (either a creature id or MeetingPlaceEmpty)
    total   \* Global meeting counter

\* ----------------------------------------------------------------------
\* Complement rule for colors
Complement(col1, col2) ==
    IF col1 = col2 THEN 
        col1
    ELSE IF (col1 = "blue"  /\ col2 = "red")    \/ (col1 = "red"    /\ col2 = "blue")    THEN "yellow"
    ELSE IF (col1 = "blue"  /\ col2 = "yellow") \/ (col1 = "yellow" /\ col2 = "blue")   THEN "red"
    ELSE IF (col1 = "red"   /\ col2 = "yellow") \/ (col1 = "yellow" /\ col2 = "red")    THEN "blue"
    ELSE Faded   \* Should never occur

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ c \in [i \in 1..N |-> [col : NonFadedColors, cnt : Nat]]
    /\ \A i \in 1..N: c[i].cnt = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature enters an empty meeting place
Enter ==
    \E i \in 1..N :
        /\ mall = MeetingPlaceEmpty
        /\ total < M
        /\ c[i].col # Faded
        /\ mall' = i
        /\ c' = c
        /\ total' = total

\* ----------------------------------------------------------------------
\* Action: after the limit is reached, a creature that tries to enter fades out
Fade ==
    \E i \in 1..N :
        /\ mall = MeetingPlaceEmpty
        /\ total = M
        /\ c[i].col # Faded
        /\ c' = [c EXCEPT ![i].col = Faded]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total

\* ----------------------------------------------------------------------
\* Action: two different creatures meet and mutate their colors
Meet ==
    \E i, j \in 1..N :
        /\ i # j
        /\ mall = j
        /\ total < M
        /\ c[i].col # Faded
        /\ c[j].col # Faded
        /\ LET newcol == Complement(c[i].col, c[j].col) IN
           /\ c' = [c EXCEPT 
                      ![i].col = newcol,
                      ![j].col = newcol,
                      ![i].cnt = @ + 1,
                      ![j].cnt = @ + 1]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty

\* ----------------------------------------------------------------------
Next ==
    \/ Enter
    \/ Fade
    \/ Meet

\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<c, mall, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ c \in [i \in 1..N |-> [col : Colors, cnt : Nat]]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M

\* ----------------------------------------------------------------------
\* Sum of meeting counts invariant
SumCounts == \Sum i \in 1..N : c[i].cnt

SumMet ==
    (total = M) => (SumCounts = 2 * M)

\* ----------------------------------------------------------------------
\* The set of invariants required by the configuration
INVARIANT TypeOK
INVARIANT SumMet

====