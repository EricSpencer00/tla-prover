---- MODULE MCTwoPhase ----
XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c
R == "R"
INSTANCE TwoPhase WITH 
    tmPrepared <- p,
    tmState    <- c,
    RM         <- {R},
    rmState    <- [R |-> c],
    msgs       <- {}
====