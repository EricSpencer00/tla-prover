---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\*-------------------------------------------------
\* Sets and basic definitions
\*-------------------------------------------------
Creatures == 1..N
BaseColors == {"blue", "red", "yellow"}
Colors == BaseColors \cup {Faded}

\* Complement rule for two colors
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE IF {c1, c2} = {"blue", "red"}   THEN "yellow"
    ELSE IF {c1, c2} = {"blue", "yellow"} THEN "red"
    ELSE "blue"

\*-------------------------------------------------
\* State variables
\*-------------------------------------------------
VARIABLES state, mall, total

vars == <<state, mall, total>>

\*-------------------------------------------------
\* Initial state
\*-------------------------------------------------
Init ==
    /\ state \in [Creatures -> [color : Colors, meetCount : Nat]]
    /\ \A c \in Creatures :
          /\ state[c].color \in BaseColors
          /\ state[c].meetCount = 0
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\*-------------------------------------------------
\* Actions
\*-------------------------------------------------
EnterEmpty ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ mall' = c
          /\ UNCHANGED <<state, total>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ \E c \in Creatures :
          /\ state[c].color # Faded
          /\ state' = [state EXCEPT ![c].color = Faded]
          /\ UNCHANGED <<mall, total>>

Meet ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
          /\ c # mall
          /\ state[c].color # Faded
          /\ state[mall].color # Faded
          /\ LET newColor == Complement(state[c].color, state[mall].color) IN
                /\ state' = [state EXCEPT
                         ![c]    = [color |-> newColor,
                                    meetCount |-> state[c].meetCount + 1],
                         ![mall] = [color |-> newColor,
                                    meetCount |-> state[mall].meetCount + 1]]
                /\ total' = total + 1
                /\ mall' = MeetingPlaceEmpty

Next == \/ EnterEmpty \/ FadeOut \/ Meet

\*-------------------------------------------------
\* Specification
\*-------------------------------------------------
Spec == Init /\ [][Next]_vars

\*-------------------------------------------------
\* Invariants
\*-------------------------------------------------
TypeOK ==
    /\ state \in [Creatures -> [color : Colors, meetCount : Nat]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    (total = M) => ( Sum({ state[c].meetCount : c \in Creatures }) = 2 * M)

====