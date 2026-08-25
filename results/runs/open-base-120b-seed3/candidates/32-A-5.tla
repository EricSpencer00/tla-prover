---- MODULE Chameneos ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, M, Faded, MeetingPlaceEmpty

\* ----------------------------------------------------------------------
\* Sets and helper definitions
\* ----------------------------------------------------------------------
BaseColors == {"blue", "red", "yellow"}
AllColors   == BaseColors \cup {Faded}

ThirdColor(c1, c2) == 
  CHOOSE c \in BaseColors : c # c1 /\ c # c2

Complement(c1, c2) == 
  IF c1 = c2 THEN c1 ELSE ThirdColor(c1, c2)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES state, mall, total

\* state : [1..N -> [color : AllColors, meetCount : Nat]]
\* mall  : either MeetingPlaceEmpty or an identifier in 1..N
\* total : Nat  (global meeting counter)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ state = [i \in 1..N |-> 
                [ color    |-> CHOOSE c \in BaseColors : TRUE,
                  meetCount|-> 0 ] ]
  /\ mall = MeetingPlaceEmpty
  /\ total = 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Enter ==
  /\ mall = MeetingPlaceEmpty
  /\ total < M
  /\ \E i \in 1..N :
        /\ state[i].color #= Faded
        /\ UNCHANGED state
        /\ mall' = i
        /\ total' = total

FadeOut ==
  /\ mall = MeetingPlaceEmpty
  /\ total >= M
  /\ \E i \in 1..N :
        /\ state[i].color #= Faded
        /\ state' = [state EXCEPT ![i].color = Faded]
        /\ mall' = MeetingPlaceEmpty
        /\ total' = total

Meet ==
  /\ mall \in 1..N                     \* a creature is waiting
  /\ total < M
  /\ \E i \in 1..N :
        /\ i # mall
        /\ state[i].color #= Faded
        /\ state[mall].color #= Faded
        /\ LET newCol == Complement(state[i].color, state[mall].color) IN
            /\ state' = [state EXCEPT 
                         ![i]    = [color |-> newCol,
                                    meetCount |-> @.meetCount + 1],
                         ![mall] = [color |-> newCol,
                                    meetCount |-> @.meetCount + 1]]
            /\ mall' = MeetingPlaceEmpty
            /\ total' = total + 1

Next == 
  \/ Enter
  \/ FadeOut
  \/ Meet

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << state, mall, total >>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ state \in [1..N -> [color : AllColors, meetCount : Nat]]
  /\ mall \in (1..N) \cup {MeetingPlaceEmpty}
  /\ total \in Nat

SumMet ==
  (total = M) => 
    ( \* sum of all individual meeting counts equals twice the number of meetings
      LET sum == +/{ i \in 1..N : state[i].meetCount } IN
        sum = 2 * M
    )

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, SumMet

====