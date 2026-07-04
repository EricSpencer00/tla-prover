---- MODULE MCTwoPhase ----
XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c, x, tmPrepared, tmState, RM, rmState, msgs
INSTANCE TwoPhase
====