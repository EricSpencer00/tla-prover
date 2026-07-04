---- MODULE MCTwoPhase ----
XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit

VARIABLES p, c, x

(*--- Substitutions for the parameters of TwoPhase ---*)
tmPrepared == {}
RM         == {}
tmState    == p
rmState    == c
msgs       == x

INSTANCE TwoPhase
====