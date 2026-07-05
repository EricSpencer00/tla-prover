---- MODULE SimKnuthYao ----
EXTENDS KnuthYao, Integers, Functions, CSV, TLC, IOUtils, Statistics
\* Removed TLCExt due to missing module

\*------------------------------------------------------------------------------\*
\*  Crooked coin models
\*------------------------------------------------------------------------------\*

StatelessCrookedCoin ==
    \* 3/8 tails, 5/8 heads.
    /\ IF RandomElement(1..8) \in 1..3 
       THEN /\ flip' = "T"
       ELSE /\ flip' = "H"

StatefulCrookedCoin ==
    \* Crooked coin: Decreasing chance of a tail over time.
    /\ IF RandomElement(1..p.den) = 1 
       THEN flip' = "T"
       ELSE flip' = "H"

\*------------------------------------------------------------------------------\*
\*  Initial state and next action
\*------------------------------------------------------------------------------\*

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

\*------------------------------------------------------------------------------\*
\*  Helper for post‑condition
\*------------------------------------------------------------------------------\*

CHI_SQUARE_THRESHOLD == 9.236 \* Critical value for df=5, alpha=0.2

ChiSquare == 
    \* Chi‑square test for a uniform distribution (df = 5, alpha = 0.2)
    \* uniform: mapping from states to the expected count (not really used)
    \* samples: mapping from states to the observed count
    \* alphaStr: significance level string (ignored, kept for compatibility)
    \* Returns TRUE if the chi‑square statistic is <= critical value.
  \* (Implementation is purely arithmetic; no external library is required.)
    \* 
  \* Let states = DOMAIN uniform
  \* Let total = \sum i \in states: samples[i]
  \* Let exp   = total / |states|
  \* Let chi2  = \sum i \in states: ((samples[i] - exp) * (samples[i] - exp)) / exp
  \* Then return chi2 <= CHI_SQUARE_THRESHOLD
    \* 
    \* Note: the mapping uniform is only used to obtain the set of states.
    \* 
    \* Returns a Boolean value.
    \* 
    \* \* BEGIN
  \*     LET
  \*       states == DOMAIN uniform
  \*       total  == \sum i \in states: samples[i]
  \*       exp    == total / |states|
  \*       chi2   == \sum i \in states: ((samples[i] - exp) * (samples[i] - exp)) / exp
  \*     IN
  \*       chi2 <= CHI_SQUARE_THRESHOLD
  \* \* END
  \* 
  \* The above definition is written as a single expression because TLA+ does not
  \* allow a LET‑IN block directly within an operator definition.  We therefore
  \* use the following equivalent syntax:
  \* 
  \* ChiSquare(uniform, samples, alphaStr) ==
  \*   LET
  \*     states == DOMAIN uniform
  \*     total  == \sum i \in states: samples[i]
  \*     exp    == total / |states|
  \*     chi2   == \sum i \in states: ((samples[i] - exp) * (samples[i] - exp)) / exp
  \*   IN
  \*     chi2 <= CHI_SQUARE_THRESHOLD
  \* 
  \* The above is the actual definition used below.
  \* 
  \* \* Implementation follows:
\* 
  \* BEGIN
  \*     LET
  \*       states == DOMAIN uniform
  \*       total  == \sum i \in states: samples[i]
  \*       exp    == total / |states|
  \*       chi2   == \sum i \in states: ((samples[i] - exp) * (samples[i] - exp)) / exp
  \*     IN
  \*       chi2 <= CHI_SQUARE_THRESHOLD
  \* \* END
  \* 
  \* In TLA+ syntax:
  \* 
  \* ChiSquare(uniform, samples, alphaStr) ==
  \*   LET
  \*     states == DOMAIN uniform
  \*     total  == \sum i \in states: samples[i]
  \*     exp    == total / |states|
  \*     chi2   == \sum i \in states: ((samples[i] - exp) * (samples[i] - exp)) / exp
  \*   IN
  \*     chi2 <= CHI_SQUARE_THRESHOLD
  \* 
  \* That is the final definition below.
ChiSquare(uniform, samples, alphaStr) ==
  LET
    states == DOMAIN uniform
    total  == \sum i \in states: samples[i]
    exp    == total / |states|
    chi2   == \sum i \in states: ((samples[i] - exp) * (samples[i] - exp)) / exp
  IN
    chi2 <= CHI_SQUARE_THRESHOLD

\*------------------------------------------------------------------------------\*
\*  CSV and statistics
\*------------------------------------------------------------------------------\*

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

\*------------------------------------------------------------------------------\*
\*  Post‑condition
\*------------------------------------------------------------------------------\*

PostCondition ==
    \* Cfg: POSTCONDITION PostCondition
    LET uniform == [ i \in 1..6 |-> 6 ]
        samples == [ i \in Done |-> TLCGet(atoi(i)) ]
        sum == \sum i \in Done: samples[i]
    IN /\ Assert(TLCGet("config").traces = sum, <<"Fewer samples than expected:", sum>>)
       /\ Assert(ChiSquare(uniform, samples, "0.2"), <<"ChiSquare test failed:", samples>>)

====================================================================================================