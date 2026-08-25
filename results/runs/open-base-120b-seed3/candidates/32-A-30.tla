---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Basic definitions
\* ----------------------------------------------------------------------
CH            == 1 .. N
Blue          == "Blue"
Red           == "Red"
Yellow        == "Yellow"
Colors        == {Blue, Red, Yellow, Faded}

\* Complement rule: if colors are equal keep it, otherwise return the third color
Complement(c1, c2) ==
    IF c1 = c2 THEN
        c1
    ELSE
        CHOOSE c \in {Blue, Red, Yellow} : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, total

vars == <<state, mall, total>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [CH -> [color : Colors, count : Nat]]
    /\ mall \in CH \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ state = [i \in CH |-> [color |-> CHOOSE c \in {Blue, Red, Yellow} : TRUE,
                               count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in CH :
          /\ state[i].color # Faded
          /\ mall' = i
          /\ UNCHANGED <<state, total>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E i \in CH :
          /\ state[i].color # Faded
          /\ state' = [state EXCEPT ![i] = [color |-> Faded,
                                            count |-> state[i].count]]
          /\ UNCHANGED mall
          /\ total' = total

Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E i \in CH :
          /\ i # mall
          /\ state[i].color # Faded
          /\ state[mall].color # Faded
          LET newc == Complement(state[i].color, state[mall].color) IN
          /\ state' = [state EXCEPT
                        ![i]    = [color |-> newc,
                                   count |-> state[i].count + 1],
                        ![mall] = [color |-> newc,
                                   count |-> state[mall].count + 1]]
          /\ total' = total + 1
          /\ mall' = MeetingPlaceEmpty

Next ==
    \/ Enter
    \/ FadeOut
    \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety property: sum of individual meeting counts equals 2*M when total = M
\* ----------------------------------------------------------------------
SumMet ==
    total = M => Sum({ state[i].count : i \in CH }) = 2 * M

=============================================================================