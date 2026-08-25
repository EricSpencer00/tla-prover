---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets of colors
\* ----------------------------------------------------------------------
PrimaryColors == {"blue", "red", "yellow"}
Colors == PrimaryColors \cup {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES creature, mall, total

\* ----------------------------------------------------------------------
\* Helper function: complement of two colors
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in PrimaryColors :
            /\ c # c1
            /\ c # c2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ creature \in [1..N -> [color : PrimaryColors, meetings : Nat]]
    /\ \A i \in 1..N: creature[i].meetings = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ creature[c].color # Faded
    /\ mall' = c
    /\ UNCHANGED <<creature, total>>

Fade(c) ==
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ creature[c].color # Faded
    /\ creature' = [creature EXCEPT ![c].color = Faded]
    /\ UNCHANGED <<mall, total>>

Meet(c) ==
    LET w == mall IN
    /\ w # MeetingPlaceEmpty
    /\ total < M
    /\ c # w
    /\ creature[c].color # Faded
    /\ creature[w].color # Faded
    /\ LET newColor == Complement(creature[c].color, creature[w].color) IN
        /\ creature' = [creature EXCEPT
                         ![c].color    = newColor,
                         ![c].meetings = @ + 1,
                         ![w].color    = newColor,
                         ![w].meetings = @ + 1]
    /\ total' = total + 1
    /\ mall' = MeetingPlaceEmpty

Next ==
    \/ \E c \in 1..N: Enter(c)
    \/ \E c \in 1..N: Fade(c)
    \/ \E c \in 1..N: Meet(c)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<creature, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ creature \in [1..N -> [color : Colors, meetings : Nat]]
    /\ mall \in (MeetingPlaceEmpty \cup 1..N)
    /\ total \in Nat

SumMet ==
    total = M => (SUM i \in 1..N: creature[i].meetings) = 2 * M
====