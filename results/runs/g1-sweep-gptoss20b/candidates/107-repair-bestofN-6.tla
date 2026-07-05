---- MODULE KnuthYao ----
EXTENDS DyadicRationals

VARIABLES p, state, flip

vars == <<p, state, flip>>

Done == {"1", "2", "3", "4", "5", "6"}
Flip == {"H", "T"}

Transition == [s0 |-> [H |-> "s1", T |-> "s2"],
               s1 |-> [H |-> "s3", T |-> "s4"],
               s2 |-> [H |-> "s5", T |-> "s6"],
               s3 |-> [H |-> "s1", T |-> "1"],
               s4 |-> [H |-> "2",  T |-> "3"],
               s5 |-> [H |-> "4",  T |-> "5"],
               s6 |-> [H |-> "6",  T |-> "s2"]]

TossCoin == flip' \in Flip

Init == /\ state = "s0"
        /\ p     = One
        /\ flip  \in Flip

CONSTANT K == 31

Next == /\ state  \notin Done
        /\ state' = Transition[state][flip]
        /\ p' = Half(p)
        /\ TossCoin
        /\ p'.den <= 2 ^ K

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* TODO Uncomment once we have a definition of DyadicRationals!DyadicRationals as tracked in https://github.com/tlaplus/CommunityModules/issues/63
\* THEOREM Converges == \A e \in DyadicRationals \ {0} : Spec => <>(state \in Done \/ p < e) 

====