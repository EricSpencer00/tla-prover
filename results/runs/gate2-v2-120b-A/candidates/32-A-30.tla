---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    N,            \* number of creatures
    M,            \* total meeting limit
    Faded,        \* the special "faded" color
    MeetingPlaceEmpty \* sentinel for empty meeting place

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Colors == {"blue", "red", "yellow", Faded}
Ids    == 1..N

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    state,        \* mapping each creature to [color |-> c, count |-> n]
    mall,         \* either MeetingPlaceEmpty or a creature Id
    total         \* total number of completed meetings

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ColorRec == [color : Colors, count : Nat]

\* complement rule:
\*   - if the two colors are the same, the result is that color
\*   - if they are different (and none is Faded), the result is the third one
Complement(c1, c2) ==
    IF c1 = Faded \/ c2 = Faded THEN Faded
    ELSE IF c1 = c2 THEN c1
    ELSE
        CHOOSE c \in {"blue", "red", "yellow"} :
            c # c1 /\ c # c2

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ mall = MeetingPlaceEmpty
    /\ total = 0
    /\ state = [i \in Ids |-> [color |-> CHOOSE c \in {"blue", "red", "yellow"} : TRUE,
                               count |-> 0]]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
EnterEmpty(i) ==
    /\ state[i].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total < M
    /\ mall' = i
    /\ UNCHANGED << state, total >>

FadeOut(i) ==
    /\ state[i].color # Faded
    /\ mall = MeetingPlaceEmpty
    /\ total = M
    /\ state' = [state EXCEPT ![i].color = Faded]
    /\ UNCHANGED << mall, total >>

MeetAndMutate(i) ==
    /\ state[i].color # Faded
    /\ mall # MeetingPlaceEmpty
    /\ mall # i
    /\ LET j == mall IN
       LET newCol == Complement(state[i].color, state[j].color) IN
       /\ state' = [state EXCEPT
                     ![i].color = newCol,
                     ![i].count = @ + 1,
                     ![j].color = newCol,
                     ![j].count = @ + 1]
    /\ mall' = MeetingPlaceEmpty
    /\ total' = total + 1

\* The overall step relation
Next ==
    \/ \E i \in Ids : EnterEmpty(i)
    \/ \E i \in Ids : FadeOut(i)
    \/ \E i \in Ids : MeetAndMutate(i)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<state, mall, total>>

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg
\* ----------------------------------------------------------------------
TypeOK ==
    /\ state \in [Ids -> ColorRec]
    /\ \A i \in Ids :
          /\ state[i].color \in Colors
          /\ state[i].count \in Nat
    /\ mall \in Ids \cup {MeetingPlaceEmpty}
    /\ total \in Nat

SumMet ==
    total = M => 
        /\ total = M
        /\ total * 2 = 
            \Sum i \in Ids : state[i].count

\* ----------------------------------------------------------------------
\* THEOREM: Spec => []SumMet   (optional, not required by .cfg)
\* ----------------------------------------------------------------------
\* THEOREM Spec => []SumMet

====