---- MODULE MCTwoPhase ----
XInit(v) == v = 0
XAct(i, xInit, xNext) == xNext = xInit
VARIABLES p, c, x

(*--- Parameters required by TwoPhase ---*)
tmPrepared == "prepared"
tmState    == [p |-> "init"]
RM         == {"rm"}
rmState    == [c |-> "init"]
msgs       == {}

INSTANCE TwoPhase WITH
    tmPrepared <- tmPrepared,
    tmState    <- tmState,
    RM         <- RM,
    rmState    <- rmState,
    msgs       <- msgs
====