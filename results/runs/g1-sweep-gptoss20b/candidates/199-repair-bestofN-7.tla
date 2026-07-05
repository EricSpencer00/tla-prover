---- MODULE MCTwoPhase ----
CONSTANT tmPrepared, tmState, RM, rmState, msgs
VARIABLES p, c, x

XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit

INSTANCE TwoPhase WITH
  tmPrepared -> tmPrepared,
  tmState -> tmState,
  RM -> RM,
  rmState -> rmState,
  msgs -> msgs
====