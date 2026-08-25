---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty, Blue, Red, Yellow

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
ColorsNoFaded == {Blue, Red, Yellow}
Colors == ColorsNoFaded \cup {Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES cmap, mall, total

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in ColorsNoFaded : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ cmap \in [1..N -> [color : Colors, count : Nat]]
    /\ mall \in {MeetingPlaceEmpty} \cup 1..N
    /\ total \in Nat
    /\ total <= M

\* ----------------------------------------------------------------------
\* Safety property: sum of individual meeting counts
\* ----------------------------------------------------------------------
SumMet ==
    total = M => 
        Sum(1..N, [i \in 1..N |-> cmap[i].count]) = 2 * M

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ cmap = [i \in 1..N |-> [color |-> CHOOSE c \in ColorsNoFaded : TRUE,
                               count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter(i) ==
    /\ i \in 1..N
    /\ cmap[i].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ mall' = i
    /\ UNCHANGED <<cmap, total>>

Fade(i) ==
    /\ i \in 1..N
    /\ cmap[i].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ cmap' = [cmap EXCEPT ![i].color = Faded]
    /\ UNCHANGED <<mall, total>>

Meet(i) ==
    /\ i \in 1..N
    /\ mall # MeetingPlaceEmpty
    /\ i # mall
    /\ cmap[i].color # Faded
    /\ cmap[mall].color # Faded
    /\ total < M
    /\ LET newColor == Complement(cmap[i].color, cmap[mall].color) IN
          /\ cmap' = [cmap EXCEPT
                        ![i].color   = newColor,
                        ![i].count   = @ + 1,
                        ![mall].color = newColor,
                        ![mall].count = @ + 1]
          /\ mall' = MeetingPlaceEmpty
          /\ total' = total + 1

Next ==
    \/ \E i \in 1..N : Enter(i)
    \/ \E i \in 1..N : Fade(i)
    \/ \E i \in 1..N : Meet(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<cmap, mall, total>>
====