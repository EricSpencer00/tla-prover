---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    N,               \* Number of creatures
    M,               \* Total meetings limit
    Faded,           \* Value representing a faded color
    MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Basic sets and definitions
\* ----------------------------------------------------------------------
Creatures == 1..N

Blue == "blue"
Red  == "red"
Yellow == "yellow"

Colors == {Blue, Red, Yellow, Faded}
ColorsNoFaded == {Blue, Red, Yellow}

\* Complement rule: same colors stay the same; different colors become the third one
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE CHOOSE c \in ColorsNoFaded : c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, total

\* state[c] = [color |-> ..., count |-> ...] for each creature c

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ state = [c \in Creatures |-> 
                    [color |-> CHOOSE col \in ColorsNoFaded : TRUE,
                     count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ mall' = c
          /\ UNCHANGED << state, total >>

Fade ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED << mall, total >>

Meet ==
    /\ \E c1 \in Creatures :
          /\ mall = c1
          /\ state[c1].color # Faded
          /\ total < M
          /\ \E c2 \in Creatures :
                /\ c2 # c1
                /\ state[c2].color # Faded
                /\ LET newcol == Complement(state[c1].color, state[c2].color) IN
                      /\ state' = [state EXCEPT 
                                    ![c1] = [color |-> newcol,
                                             count |-> @.count + 1],
                                    ![c2] = [color |-> newcol,
                                             count |-> @.count + 1]]
                /\ total' = total + 1
                /\ mall' = MeetingPlaceEmpty

Next == Enter \/ Fade \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_<<state, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [Creatures -> [color: Colors, count: Nat]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat
    /\ total <= M
    /\ \A c \in Creatures : state[c].color \in Colors
    /\ \A c \in Creatures : state[c].count \in Nat

SumMet ==
    /\ total = M
    /\ Sum(Creatures, LAMBDA c : state[c].count) = 2 * M

====