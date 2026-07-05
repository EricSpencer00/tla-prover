---- MODULE KnuthYao ----
\* =================================================================
\* Knuth–Yao algorithm: a discrete‑time Markov process over
\* states s0..s6 and absorbing output states 1..6.
\* =================================================================
EXTENDS DyadicRationals

VARIABLES p,      \* The probability we are here
          state,   \* The current state (a string)
          flip     \* The current flip (“H” or “T”)

vars == <<p, state, flip>>

\* The terminal output states
Done == {"1", "2", "3", "4", "5", "6"}

\* The possible coin outcomes
Flip == { "H", "T" }

\* Transition relation: a deterministic function of the
\* current state and the current flip.
Transition == [ "s0" |-> [H |-> "s1", T |-> "s2"],
                "s1" |-> [H |-> "s3", T |-> "s4"],
                "s2" |-> [H |-> "s5", T |-> "s6"],
                "s3" |-> [H |-> "s1", T |-> "1" ],
                "s4" |-> [H |-> "2",  T |-> "3" ],
                "s5" |-> [H |-> "4",  T |-> "5" ],
                "s6" |-> [H |-> "6",  T |-> "s2"] ]

\* One step of the process
TossCoin == flip' \in Flip

Init == /\ state = "s0"
        /\ p     = One
        /\ flip  \in Flip

Next == /\ state  \notin Done
        /\ state' = Transition[state][flip]
        /\ p'     = Half(p)
        /\ TossCoin

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* The following theorem is a sketch of the algorithm’s
\* convergence; it is left commented because the dyadic
\* rational arithmetic is not yet fully available in the
\* community modules.
\* THEOREM Converges == \A e \in DyadicRationals \ {0} :
\*                      Spec => <>(state \in Done \/ p < e)

====