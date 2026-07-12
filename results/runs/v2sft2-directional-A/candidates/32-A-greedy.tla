---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Color == {"blue", "red", "yellow", Faded}
Creatures == 1..N

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, mp, total

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ColorOf(c) == state[c][1]
MeetCount(c) == state[c][2]

\* Complement rule: if colors are equal, keep that color; otherwise
\* pick the third color not held by either.
Complement(c1, c2) ==
    IF c1 = c2 THEN c1
    ELSE
        CHOOSE c \in Color \ {c1, c2, Faded} : TRUE

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ state = [c \in Creatures |-> [1 \in Color \ {Faded} : c, 0]]
    /\ mp = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty ==
    /\ mp = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
          /\ state[c][1] # Faded
          /\ mp' = c
          /\ UNCHANGED <<state, total>>

FadeOut ==
    /\ mp = MeetingPlaceEmpty
    /\ total >= M
    /\ \E c \in Creatures :
          /\ state[c][1] # Faded
          /\ state' = [state EXCEPT ![c][1] = Faded]
          /\ UNCHANGED <<mp, total>>

MeetAndMutate ==
    /\ mp # MeetingPlaceEmpty
    /\ \E c \in Creatures :
          /\ c # mp
          /\ state[c][1] # Faded
          /\ state[mp][1] # Faded
          /\ LET newColor == Complement(state[c][1], state[mp][1]) IN
             /\ state' = [state EXCEPT ![c][1] = newColor,
                                      ![c][2] = state[c][2] + 1,
                                      ![mp][1] = newColor,
                                      ![mp][2] = state[mp][2] + 1]
             /\ mp' = MeetingPlaceEmpty
             /\ total' = total + 1

Next ==
    \/ EnterEmpty
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mp, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [Creatures -> [1 |-> Color, 2 |-> Nat]]
    /\ mp \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual meeting counts equals twice the
\* global meeting counter when the global counter reaches the limit
\* ----------------------------------------------------------------------
SumMet ==
    total >= M => (SUM c \in Creatures : MeetCount(c)) = 2 * total

====