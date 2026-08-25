---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    N,               \* Number of creatures (positive integer)
    M,               \* Maximum total number of meetings (positive integer)
    Faded,           \* Symbol representing a faded creature's color
    MeetingPlaceEmpty \* Symbol representing an empty meeting place

\* ----------------------------------------------------------------------
\* Colors used by non‑faded creatures
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow"}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    state,   \* Mapping from each creature (1..N) to a record [color, count]
    mall,    \* Current occupant of the meeting place (a creature id or MeetingPlaceEmpty)
    total    \* Global counter of completed meetings

\* ----------------------------------------------------------------------
\* Helper: complement rule for two colors
\* ----------------------------------------------------------------------
Complement(c1, c2) == 
    IF c1 = c2 THEN c1 
    ELSE CHOOSE c \in Colors : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ state = [i \in 1..N |-> [color |-> CHOOSE c \in Colors : TRUE,
                                 count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature enters an empty meeting place (while meetings remain)
\* ----------------------------------------------------------------------
Enter(i) == 
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ i \in 1..N
    /\ state[i].color # Faded
    /\ mall' = i
    /\ UNCHANGED <<state, total>>

\* ----------------------------------------------------------------------
\* Action: a non‑faded creature tries to enter after the limit and fades out
\* ----------------------------------------------------------------------
Fade(i) == 
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ i \in 1..N
    /\ state[i].color # Faded
    /\ state' = [state EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<mall, total>>

\* ----------------------------------------------------------------------
\* Action: a creature arrives while another is waiting; they meet and mutate
\* ----------------------------------------------------------------------
Meet(i) == 
    LET j == mall IN
    /\ mall # MeetingPlaceEmpty               \* there is a waiting creature
    /\ total < M
    /\ i \in 1..N
    /\ i # j                                 \* cannot meet itself
    /\ state[i].color # Faded
    /\ state[j].color # Faded
    /\ LET newCol == Complement(state[i].color, state[j].color) IN
       /\ state' = [state EXCEPT 
                     ![i].color = newCol,
                     ![i].count = @ + 1,
                     ![j].color = newCol,
                     ![j].count = @ + 1]
       /\ mall' = MeetingPlaceEmpty
       /\ total' = total + 1

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    \/ \E i \in 1..N: Enter(i)
    \/ \E i \in 1..N: Fade(i)
    \/ \E i \in 1..N: Meet(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ state \in [1..N -> [color : Colors \cup {Faded}, count : Nat]]
    /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual meeting counts equals twice the total meetings
\* ----------------------------------------------------------------------
SumMet == 
    total = M => (\Sum i \in 1..N: state[i].count) = 2 * M

====