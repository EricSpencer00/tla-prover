---- MODULE MCTwoPhase ----
XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c, x

(*--- Parameter bindings for the TwoPhase instance ---*)
RM        == p
rmState   == c
tmPrepared == x
tmState   == x
msgs      == {}

INSTANCE TwoPhase
====