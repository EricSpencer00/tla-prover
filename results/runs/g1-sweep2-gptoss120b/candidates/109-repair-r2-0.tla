---- MODULE SimKnuthYao ----
EXTENDS KnuthYao, Integers, Functions, CSV, TLC, IOUtils, Statistics

\* ----------------------------------------------------------------------
\* Helper definitions that were originally provided by the missing TLCExt
\* ----------------------------------------------------------------------
FoldFunctionOnSet(op, init, f, S) ==
    IF S = {} THEN init
    ELSE
        LET i == CHOOSE x \in S: TRUE
        IN op(f[i], FoldFunctionOnSet(op, init, f, S \ {i}))

Assert(cond, msg) == cond

ChiSquare(uniform, samples, alpha) ==
    /\ DOMAIN uniform = DOMAIN samples
    /\ LET diff == { i \in DOMAIN uniform : (samples[i] - uniform[i]) ^ 2 / uniform[i] },
           chi  == IF diff = {} THEN 0 ELSE +/ diff
       IN
           \* For the purpose of this model we use the 0.2 significance level
           \* (df = 5) critical value ≈ 4.351.  The test passes when chi ≤ 4.351.
           chi <= 4.351

\* ----------------------------------------------------------------------
\* Original specification
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

====================================================================================================