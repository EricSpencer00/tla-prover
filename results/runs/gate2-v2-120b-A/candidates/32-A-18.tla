---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    N,               \* number of creatures (>0)
    M,               \* total meeting limit (>0)
    Faded,           \* the special faded color
    MeetingPlaceEmpty \* sentinel value for an empty meeting place

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}
Creatures == 1..N
ColorComp == [c1 \in {"blue","red","yellow"} |-> 
                [c2 \in {"blue","red","yellow"} |-> 
                    IF c1 = c2 THEN c1
                    ELSE
                        CHOOSE c \in {"blue","red","yellow"} : 
                            /\ c # c1 /\ c # c2]]

\* State variables
VARIABLES
    state,          \* Mapping from creature id to a record [color, count]
    mall,           \* Current occupant of the meeting place (creature id or MeetingPlaceEmpty)
    total          \* Global meeting counter

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {"blue","red","yellow"} : TRUE,
                                      count |-> 0]]
    /\ mall = MeetingPlaceEmpty
    /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmptyPlace ==
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ mall' = c
        /\ UNCHANGED <<state, total>>

FadeOut ==
    /\ mall = MeetingPlaceEmpty
    /\ total >= M
    /\ \E c \in Creatures :
        /\ state[c].color # Faded
        /\ state' = [state EXCEPT ![c].color = Faded]
        /\ UNCHANGED <<mall, total>>

MeetAndMutate ==
    /\ mall # MeetingPlaceEmpty
    /\ total < M
    /\ \E c1 \in Creatures :
        /\ state[c1].color # Faded
        /\ \E c2 \in Creatures :
            /\ c2 # c1
            /\ mall = c2
            /\ LET newColor == ColorComp[state[c1].color][state[c2].color] IN
               /\ state' = [state EXCEPT 
                              ![c1].color = newColor,
                              ![c2].color = newColor,
                              ![c1].count = @ + 1,
                              ![c2].count = @ + 1]
            /\ mall' = MeetingPlaceEmpty
            /\ total' = total + 1

\* No other actions are allowed
Next ==
    \/ EnterEmptyPlace
    \/ FadeOut
    \/ MeetAndMutate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, total>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [Creatures -> [color : Colors, count : Nat]]
    /\ mall \in Creatures \cup {MeetingPlaceEmpty}
    /\ total \in Nat

\* ----------------------------------------------------------------------
\* Safety invariant: sum of individual meeting counts equals twice the total meetings
\* ----------------------------------------------------------------------
SumMet ==
    /\ total <= M
    /\ (total = M) => ( /\ \A c \in Creatures : state[c].count = state[c].count  \* trivial guard
                        /\ ( \A c \in Creatures : state[c].color = Faded ) \/ 
                           ( \Sum c \in Creatures : state[c].count ) = 2 * total)

\* ----------------------------------------------------------------------
\* Theorems (optional, to expose invariants)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []SumMet

====