---- MODULE MCTwoPhase ----
VARIABLES p, c, x, rmState, msgs

XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit

INSTANCE TwoPhase [tmPrepared -> p, tmState -> c, RM -> x, rmState -> rmState, msgs -> msgs]
====