---- MODULE Chameneos ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Set of creature identifiers
\* ----------------------------------------------------------------------
Creatures == 1..N

\* ----------------------------------------------------------------------
\* Colors
\* ----------------------------------------------------------------------
Blue == "blue"
Red  == "red"
Yellow == "yellow"
Colors == {Blue, Red, Yellow, Faded}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, total

vars == << state, mall, total >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
NonFaded(c) == state[c].color # Faded

Complement(c1, c2) ==
  IF c1 = c2 THEN
    c1
  ELSE IF (c1 = Blue /\ c2 = Red) \/ (c1 = Red /\ c2 = Blue) THEN
    Yellow
  ELSE IF (c1 = Blue /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Blue) THEN
    Red
  ELSE IF (c1 = Red /\ c2 = Yellow) \/ (c1 = Yellow /\ c2 = Red) THEN
    Blue
  ELSE
    Faded \* should never happen for non‑faded inputs

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state = [c \in Creatures |-> [color |-> CHOOSE col \in {Blue, Red, Yellow} : TRUE,
                                   meetCount |-> 0]]
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
  /\ mall # MeetingPlaceEmpty            \* a creature is waiting
  /\ total < M
  /\ \E c2 \in Creatures :
        /\ c2 # mall
        /\ state[c2].color # Faded
        LET c1 == mall IN
        LET newColor == Complement(state[c1].color, state[c2].color) IN
        /\ state' = [c \in Creatures |-> 
                      IF c = c1 \/ c = c2
                      THEN [color |-> newColor,
                            meetCount |-> state[c].meetCount + 1]
                      ELSE state[c]]
        /\ total' = total + 1
        /\ mall' = MeetingPlaceEmpty

Next == \/ Enter \/ Fade \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [Creatures -> [color : Colors, meetCount : Nat]]
  /\ mall \in Creatures \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  (total = M) => 
    ( \* sum of all individual meeting counts equals twice the number of meetings
      LET sum == Sum({c \in Creatures : state[c].meetCount}) IN
      sum = 2 * M )

\* ----------------------------------------------------------------------
\* Theorem for TLC (optional)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====