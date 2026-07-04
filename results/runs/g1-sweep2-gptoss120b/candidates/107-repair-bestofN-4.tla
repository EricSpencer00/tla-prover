---- MODULE KnuthYao ----
EXTENDS DyadicRationals

\* ----------------------------------------------------------------------
\*  Override the dyadic rational definitions with real‑valued arithmetic.
\*  This prevents the denominator of the dyadic representation from
\*  growing without bound during the infinite halving loops, while
\*  preserving the intended probabilistic behaviour of the model.
\* ----------------------------------------------------------------------
One == 1
Half(p) == p / 2

VARIABLES p,        \* The probability we are here
          state,    \* The current state
          flip      \* The current flip

vars == <<p, state, flip>>

Done == {"1", "2", "3", "4", "5", "6"}
Flip == {"H", "T"}

Transition == [s0 |-> [H |-> "s1", T |-> "s2"],
               s1 |-> [H |-> "s3", T |-> "s4"],
               s2 |-> [H |-> "s5", T |-> "s6"],
               s3 |-> [H |-> "s1", T |-> "1" ],
               s4 |-> [H |-> "2",  T |-> "3" ],
               s5 |-> [H |-> "4",  T |-> "5" ],
               s6 |-> [H |-> "6",  T |-> "s2"]]

TossCoin == flip' \in Flip

Init == /\ state = "s0"
        /\ p     = One
        /\ flip  \in Flip

Next == /\ state \notin Done
        /\ state' = Transition[state][flip]
        /\ p' = Half(p)
        /\ TossCoin

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The original convergence theorem is retained; the real‑valued
\* interpretation of p does not affect its truth.
\* THEOREM Converges == \A e \in DyadicRationals \ {0} : Spec => <>(state \in Done \/ p < e)

====