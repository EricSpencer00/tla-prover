---- MODULE Chameneos ----
EXTENDS Naturals

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* Creatures (chameneos) gather at a central meeting place (the Mall) and engage in pairwise
\* meetings. The complement rule is deterministic for every unordered pair of colors: if both
\* participants share a color they keep it, otherwise they both adopt the third color. A global
\* meeting counter caps the number of meetings; when it is reached, creatures simply fade out
\* instead of entering. A faded creature no longer participates. Because a meeting always
\* involves exactly two participants, the sum of individuals' meeting counts is twice the
\* number of meetings that actually occurred.
Colors == {"blue", "red", "yellow"}

VARIABLES state, occupant, totalMet

vars == << state, occupant, totalMet >>

\* The complement of two colors: the third color in the set, or the same if both are equal.
Complement(a, b) ==
    IF a = b THEN a
    ELSE CHOOSE c \in Colors : c # a /\ c # b

InitState == CHOOSE s \in {"blue", "red", "yellow"} : s

Init ==
    /\ state = [c \in 1..N |-> << InitState, 0 >>]
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet = 0

Enter(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet < M
    /\ state[c][1] # Faded
    /\ occupant' = c
    /\ UNCHANGED << state, totalMet >>

Fade(c) ==
    /\ occupant = MeetingPlaceEmpty
    /\ totalMet >= M
    /\ state[c][1] # Faded
    /\ state' = [state EXCEPT ![c][1] = Faded]
    /\ UNCHANGED << occupant, totalMet >>

\* When a waiting creature meets an arriver, both adopt the pairwise complement and both
\* individual meeting counters, as well as the global counter, advance by one.
Meet(c) ==
    /\ occupant # MeetingPlaceEmpty
    /\ occupant # c
    /\ state[c][1] # Faded
    /\ LET a == state[occupant] IN
        LET b == state[c] IN
            LET newColor == Complement(a[1], b[1]) IN
                /\ state' = [state EXCEPT ![occupant][1] = newColor, ![c][1] = newColor,
                                    ![occupant][2] = a[2] + 1, ![c][2] = b[2] + 1]
                /\ totalMet' = totalMet + 1
    /\ occupant' = MeetingPlaceEmpty

Next ==
    \/ \E c \in 1..N : Enter(c)
    \/ \E c \in 1..N : Fade(c)
    \/ \E c \in 1..N : Meet(c)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ state \in [1..N -> (Colors \cup {Faded}) \X (0..M)]
    /\ occupant \in (1..N) \cup {MeetingPlaceEmpty}
    /\ totalMet \in 0..M

SumMet ==
    IF totalMet = M
    THEN LET g(S) ==
                IF S = {} THEN 0
                ELSE LET x == CHOOSE y \in S : TRUE IN state[x][2] + g(S \ {x})
         IN g(1..N) = 2 * M
    ELSE TRUE

====