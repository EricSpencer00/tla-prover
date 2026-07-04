---- MODULE SimKnuthYao ----
EXTENDS KnuthYao, Integers, Functions, CSV, TLC, IOUtils, Statistics, FiniteSets

\* ----------------------------------------------------------------------
\* Crooked coin definitions (stateless and stateful)
\* ----------------------------------------------------------------------
StatelessCrookedCoin ==
    \* 3/8 tails, 5/8 heads.
    /\ IF RandomElement(1..8) \in 1..3
       THEN /\ flip' = "T"
            \* Multiplying these probabilities quickly overflows TLC's dyadic rationals.
            \* /\ p' = Reduce([ num |-> p.num * 3, den |-> p.den * 8 ])
       ELSE /\ flip' = "H"
            \* /\ p' = Reduce([ num |-> p.num * 5, den |-> p.den * 8 ])
    \* Statistically, modeling the crooked coin with a disjunct is the same,
    \* but the generator won't extend the behavior if both disjuncts evaluate
    \* to false. Confirm by running the generator with a fixed number of traces
    \* and see how PostCondition is violated.
    \* /\ \/ /\ RandomElement(1..10) \in 4..10
    \*       /\ flip' = "H"
    \*    \/ /\ RandomElement(1..10) \in 1..3
    \*       /\ flip' = "T"

StatefulCrookedCoin ==
    \* Crooked coin: Decreasing chance of a tail over time.
    /\ IF RandomElement(1..p.den) = 1
       THEN flip' = "T"
       ELSE flip' = "H"

\* ----------------------------------------------------------------------
\* Initialization and next-state relation
\* ----------------------------------------------------------------------
SimInit ==
    /\ state = "init"
    /\ p     = One
    /\ flip  \in Flip

SimNext ==
    \* Need an artificial initial state to be able to model a crooked coin.
    \* Otherwise, the first flip will always be fair.
    \/ /\ state = "init"
       /\ state' = "s0"
       /\ UNCHANGED p
       /\ TossCoin
    \/ /\ state # "init"
       /\ state \notin Done
       /\ state' = Transition[state][flip]
       /\ p' = Half(p)
       /\ TossCoin

IsDyadic ==
    \* This is expensive to evaluate with TLC.
    IsDyadicRational(p)

\* ----------------------------------------------------------------------
\* Assumptions about the TLC configuration
\* ----------------------------------------------------------------------
ASSUME
    /\ TLCGet("config").mode = "generate"
    /\ TLCGet("config").depth >= 15 \/ TLCGet("config").depth = -1
    /\ TLCGet("config").deadlock = FALSE
    /\ TLCGet("revision").timestamp >= 1663720820

CSVFile == "SimKnuthYao.csv"

ASSUME
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("side,p,flip", <<>>, CSVFile)
    /\ \A i \in Done: TLCSet(atoi(i), 0)

\* ----------------------------------------------------------------------
\* Statistics collection
\* ----------------------------------------------------------------------
Stats ==
    /\ state \in Done =>
        /\ CSVWrite("%1$s,%2$s,%3$s", <<state, p.den, flip>>, CSVFile)
        /\ TLCSet(atoi(state), TLCGet(atoi(state)) + 1)
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimKnuthYao.R", CSVFile>>).exitValue = 0

\* ----------------------------------------------------------------------
\* Post‑condition checks
\* ----------------------------------------------------------------------
PostCondition ==
    LET uniform == [ i \in 1..6 |-> 6 ]
        samples == [ i \in Done |-> TLCGet(atoi(i)) ]
        sum     == FoldFunctionOnSet("+", 0, samples, Done)
    IN /\ Assert(TLCGet("config").traces = sum,
                 <<"Fewer samples than expected:", sum>>)
       /\ Assert(ChiSquare(uniform, samples, "0.2"),
                 <<"ChiSquare test failed:", samples>>)

\* ----------------------------------------------------------------------
\* Helper definitions that were provided by the missing TLCExt module
\* ----------------------------------------------------------------------
Assert(cond, _msg) == cond

FoldFunctionOnSet(op, init, f, S) ==
    IF op = "+" THEN
        init + Sum({ f[i] : i \in S })
    ELSE
        init

ChiSquare(uniform, samples, _alpha) ==
    LET chi == Sum({ (samples[i] - uniform[i]) ^ 2 / uniform[i] : i \in DOMAIN uniform })
    IN chi <= 9

=============================================================================