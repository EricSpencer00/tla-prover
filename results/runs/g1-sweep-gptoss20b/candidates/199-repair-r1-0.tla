---- MODULE MCTwoPhase ----
CONSTANTS
  RM = {"rm1"},
  msgs = {"msg1"},
  tmState = {"prepared", "committed", "aborted"},
  tmPrepared = {"prepared"},
  rmState = [r \in RM |-> "prepared"]

XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c, x
INSTANCE TwoPhase WITH tmPrepared -> tmPrepared, tmState -> tmState, RM -> RM, rmState -> rmState, msgs -> msgs
====