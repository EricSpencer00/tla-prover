---- MODULE MCTwoPhase ----
EXTENDS Naturals

XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit

VARIABLES p, c, x

INSTANCE TwoPhase WITH
    tmPrepared <- {},
    tmState    <- "init",
    RM         <- {},
    rmState    <- [r \in {} |-> "init"],
    msgs       <- {}

====