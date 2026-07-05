---- MODULE MCTwoPhase ----
CONSTANT RM
VARIABLES p, c, x, msgs

XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit

INSTANCE TwoPhase WITH
  tmPrepared -> p,
  tmState -> c,
  RM -> RM,
  rmState -> x,
  msgs -> msgs
====