---- MODULE MCTwoPhase ----
CONSTANT RM = {1}

XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c, x, tmPrepared, tmState, rmState, msgs
INSTANCE TwoPhase
====