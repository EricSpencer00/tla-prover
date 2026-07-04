---- MODULE MCTwoPhase ----
XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c, x
INSTANCE TwoPhase WITH 
    tmPrepared <- p,
    tmState    <- c,
    RM         <- {x},
    rmState    <- [x |-> c],
    msgs       <- {}
====