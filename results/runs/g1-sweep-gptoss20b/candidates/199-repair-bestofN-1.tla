---- MODULE MCTwoPhase ----
CONSTANTS tmPrepared, tmState, RM, rmState, msgs

XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c, x
INSTANCE TwoPhase
====