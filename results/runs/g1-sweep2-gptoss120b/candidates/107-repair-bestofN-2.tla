---- MODULE KnuthYao ----
EXTENDS DyadicRationals

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES p,          \* The probability we are here
          state,      \* The current state
          flip,       \* The current flip
          steps       \* Number of coin‑toss steps taken so far

\* ----------------------------------------------------------------------
\* State vector
\* ----------------------------------------------------------------------
vars == <<p, state, flip, steps>>

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
Done == {"1", "2", "3", "4", "5", "6"}
Flip == {"H", "T"}

\* Upper bound on the number of halving steps.  This bound is only a
\* practical device for model checking; it does not affect the logical
\* meaning of the specification for runs that terminate before the bound.
MaxSteps == 10

\* ----------------------------------------------------------------------
\* Transition function (the Knuth‑Yao tree)
\* ----------------------------------------------------------------------
Transition == [s0 |-> [H |-> "s1", T |-> "s2"],
               s1 |-> [H |-> "s3", T |-> "s4"],
               s2 |-> [H |-> "s5", T |-> "s6"],
               s3 |-> [H |-> "s1", T |-> "1" ],
               s4 |-> [H |-> "2",  T |-> "3" ],
               s5 |-> [H |-> "4",  T |-> "5" ],
               s6 |-> [H |-> "6",  T |-> "s2"]]

\* ----------------------------------------------------------------------
\* Action: a coin toss
\* ----------------------------------------------------------------------
TossCoin == flip' \in Flip

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == /\ state = "s0"
        /\ p    = One
        /\ flip \in Flip
        /\ steps = 0

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == /\ state \notin Done
        /\ state' = Transition[state][flip]
        /\ IF steps < MaxSteps
              THEN p' = Half(p)
              ELSE p' = p
        /\ steps' = steps + 1
        /\ TossCoin

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* TODO Uncomment once we have a definition of DyadicRationals!DyadicRationals
\* as tracked in https://github.com/tlaplus/CommunityModules/issues/63
\* THEOREM Converges == \A e \in DyadicRationals \ {0} : Spec => <>(state \in Done \/ p < e)

====