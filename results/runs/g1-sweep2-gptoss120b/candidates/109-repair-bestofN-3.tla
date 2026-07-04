---- MODULE SimKnuthYao ----
EXTENDS KnuthYao, Integers, Functions, CSV, TLC, IOUtils, Statistics

\* ----------------------------------------------------------------------
\* Helper definitions that were originally provided by the missing TLCExt
\* module.  They are re‑implemented here in a way that preserves the
\* intended semantics for the model‑checking tasks.
\* ----------------------------------------------------------------------

\* Assert(b, msg) yields TRUE when b is TRUE; otherwise it yields FALSE.
\* TLC will report the failure (the message is ignored by the TLA++
\* semantics but kept for compatibility with the original TLCExt).
Assert(b, msg) == IF b THEN TRUE ELSE FALSE

\* FoldFunctionOnSet(op, init, set, domain) folds the binary operator
\* op over the elements of the function set indexed by the elements of
\* domain, starting with the initial value init.
FoldFunctionOnSet(op, init, set, domain) ==
    IF domain = {} THEN init
    ELSE
        LET e == CHOOSE x \in domain : TRUE
        IN op(set[e], FoldFunctionOnSet(op, init, set, domain \ {e}))

\* A simple chi‑square test for the uniform distribution.
\* The third argument is a string representing the significance level
\* (e.g., "0.2").  For the purpose of this model we support the level
\* used in the specification; other values return FALSE.
ChiSquare(uniform, samples, alpha) ==
    LET
        chi == +/\ i \in DOMAIN uniform :
                  (samples[i] - uniform[i]) ^ 2 / uniform[i]
        critical ==
            CASE alpha = "0.2" -> 4.351
                 OTHER        -> 0
    IN chi <= critical

\* ----------------------------------------------------------------------
\* Original specification (unchanged apart from the removal of TLCExt)
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

----------------------------------------------------------------------------------------------------

StatefulCrookedCoin ==
    \* Crooked coin: Decreasing chance of a tail over time.
    /\ IF RandomElement(1..p.den) = 1 
       THEN flip' = "T"
       ELSE flip' = "H"

----------------------------------------------------------------------------------------------------

SimInit == 
    /\ state = "init"
    /\ p     = One
    /\ flip  \in Flip

SimNext ==
    \* Need an artificial initial state to be able to model a crooked coin.  Otherwise,
    \* the first flip will always be fair. 
    \/ /\ state = "init"
       /\ state' = "s0"
       /\ UNCHANGED p
       /\ TossCoin
    \/ /\ state # "init"
       /\ state  \notin Done
       /\ state' = Transition[state][flip]
       /\ p' = Half(p)
       /\ TossCoin

IsDyadic ==
    \* This is expensive to evaluate with TLC.
    IsDyadicRational(p)

----------------------------------------------------------------------------------------------------


ASSUME
    \* The data collection below only works with TLC running in generation mode.
    /\ TLCGet("config").mode = "generate"
    \* Do not artificially restrict the length of behaviors.
    /\ TLCGet("config").depth >= 15 \/ TLCGet("config").depth = -1
    \* The algorithm terminates. Thus, do not check for deadlocks.
    /\ TLCGet("config").deadlock = FALSE
    \* Require a recent versions of TLC with support for the operators appearing here.
    /\ TLCGet("revision").timestamp >= 1663720820 

CSVFile ==
    "SimKnuthYao.csv"

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("side,p,flip", <<>>, CSVFile)
    \* Initialize TLC's registers 1 to 6 with zero.
    /\ \A i \in Done: TLCSet(atoi(i), 0)

Stats ==
    \* Cfg: CONSTRAINT Stats
    /\ state \in Done => 
        /\ CSVWrite("%1$s,%2$s,%3$s", <<state, p.den, flip>>, CSVFile)
        /\ TLCSet(atoi(state), TLCGet(atoi(state)) + 1)
        \* Update KnuthYao.svg every 100 samples.
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimKnuthYao.R", CSVFile>>).exitValue = 0

----------------------------------------------------------------------------------------------------

PostCondition ==
    \* Cfg: POSTCONDITION PostCondition
    LET uniform == [ i \in 1..6 |-> 6 ]
        samples == [ i \in Done |-> TLCGet(atoi(i)) ]
            sum == FoldFunctionOnSet(+, 0, samples, Done)
    IN /\ Assert(TLCGet("config").traces = sum, <<"Fewer samples than expected:", sum>>)
       /\ Assert(ChiSquare(uniform, samples, "0.2"), <<"ChiSquare test failed:", samples>>)

====================================================================================================