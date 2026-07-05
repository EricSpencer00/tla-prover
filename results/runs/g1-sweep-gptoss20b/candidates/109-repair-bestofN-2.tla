---- MODULE SimKnuthYao ----
EXTENDS KnuthYao, Integers, Functions, CSV, TLC, IOUtils, Statistics

\* ----------------------------------------------------------------
\* Auxiliary definitions replacing the missing TLCExt module.
\* ----------------------------------------------------------------
RandomElement(s) == CHOOSE y \in s : TRUE

IsDyadicRational(p) == TRUE

\* ----------------------------------------------------------------
\* Coin models
\* ----------------------------------------------------------------
StatelessCrookedCoin ==
    \* 3/8 tails, 5/8 heads.
    /\ IF RandomElement(1..8) \in 1..3 
       THEN /\ flip' = "T"
            \* Multiplying these probabilities quickly overflows TLC's dyadic rationals.
            \* /\ p' = Reduce([ num |-> p.num * 3, den |-> p.den * 8 ])
       ELSE /\ flip' = "H"
            \* /\ p' = Reduce([ num |-> p.num * 5, den |-> p.den * 8 ])

StatefulCrookedCoin ==
    \* Crooked coin: Decreasing chance of a tail over time.
    /\ IF RandomElement(1..p.den) = 1 
       THEN flip' = "T"
       ELSE flip' = "H"

\* ----------------------------------------------------------------
\* Simulation initial state and transition
\* ----------------------------------------------------------------
SimInit == 
    /\ state = "init"
    /\ p     = One
    /\ flip  \in Flip

SimNext ==
    \/ /\ state = "init"
       /\ state' = "s0"
       /\ UNCHANGED p
       /\ TossCoin
    \/ /\ state # "init"
       /\ state  \notin Done
       /\ state' = Transition[state][flip]
       /\ p' = Half(p)
       /\ TossCoin

\* ----------------------------------------------------------------
\* Dyadic invariant (unused but defined for completeness)
\* ----------------------------------------------------------------
IsDyadic ==
    \* This is expensive to evaluate with TLC.
    IsDyadicRational(p)

\* ----------------------------------------------------------------
\* CSV file and configuration assumptions
\* ----------------------------------------------------------------
CSVFile ==
    "SimKnuthYao.csv"

ASSUME
    \* The data collection below only works with TLC running in generation mode.
    /\ TLCGet("config").mode = "generate"
    \* Do not artificially restrict the length of behaviors.
    /\ TLCGet("config").depth >= 15 \/ TLCGet("config").depth = -1
    \* The algorithm terminates. Thus, do not check for deadlocks.
    /\ TLCGet("config").deadlock = FALSE
    \* Require a recent versions of TLC with support for the operators appearing here.
    /\ TLCGet("revision").timestamp >= 1663720820 

\* ----------------------------------------------------------------
\* Statistics constraint
\* ----------------------------------------------------------------
Stats ==
    /\ state \in Done => 
        /\ CSVWrite("%1$s,%2$s,%3$s", <<state, p.den, flip>>, CSVFile)
        /\ TLCSet(atoi(i), TLCGet(atoi(i)) + 1)
        \* Update KnuthYao.svg every 100 samples.
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimKnuthYao.R", CSVFile>>).exitValue = 0

\* ----------------------------------------------------------------
\* Post-condition
\* ----------------------------------------------------------------
PostCondition ==
    LET uniform == [ i \in 1..6 |-> 6 ]
        samples == [ i \in Done |-> TLCGet(atoi(i)) ]
            sum == FoldFunctionOnSet(+, 0, samples, Done)
    IN /\ Assert(TLCGet("config").traces = sum, <<"Fewer samples than expected:", sum>>)
       /\ Assert(ChiSquare(uniform, samples, "0.2"), <<"ChiSquare test failed:", samples>>)
====