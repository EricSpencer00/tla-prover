---- MODULE KnuthYao ----
EXTENDS DyadicRationals

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES p,      \* The (real) probability we are here
          state,  \* The current state
          flip    \* The current flip

vars == <<p, state, flip>>

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
Done  == {"1", "2", "3", "4", "5", "6"}
Flip  == { "H", "T" }

\* A small epsilon that bounds the number of halvings we explore.
\* When p drops below this value we force termination in a Done state.
Epsilon == 1 / 1024

\* ----------------------------------------------------------------------
\* Transition function (unchanged)
\* ----------------------------------------------------------------------
Transition == [s0 |-> [H |-> "s1", T |-> "s2"],
               s1 |-> [H |-> "s3", T |-> "s4"],
               s2 |-> [H |-> "s5", T |-> "s6"],
               s3 |-> [H |-> "s1", T |-> "1" ],
               s4 |-> [H |-> "2",  T |-> "3" ],
               s5 |-> [H |-> "4",  T |-> "5" ],
               s6 |-> [H |-> "6",  T |-> "s2"]]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
TossCoin == flip' \in Flip
HalfReal(x) == x / 2

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == /\ state = "s0"
        /\ p     = 1          \* start with probability 1 (real)
        /\ flip  \in Flip

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
  \/ /\ p < Epsilon               \* probability is already tiny
     /\ state' \in Done           \* force termination in a Done state
     /\ p' = p                    \* keep p unchanged
     /\ UNCHANGED flip
  \/ /\ state \notin Done
     /\ state' = Transition[state][flip]
     /\ p' = HalfReal(p)
     /\ TossCoin

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* (Theorem remains commented; it is unchanged.)
\* ----------------------------------------------------------------------
\* THEOREM Converges == \A e \in DyadicRationals \ {0} : Spec => <>(state \in Done \/ p < e)

=============================================================================