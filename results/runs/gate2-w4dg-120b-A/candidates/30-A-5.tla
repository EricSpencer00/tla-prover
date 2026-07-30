---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, vprop, vpropstar, vdec, crashed, msgs, recv

vars == <<loc, view, vprop, vpropstar, vdec, crashed, msgs, recv>>

MsgPhases == {"ph1", "ph2"}

TypeOK ==
    /\ loc \in [1..N -> {"broad1", "ph1wait", "prepare", "broad2",
                         "ph2wait", "done", "crashed", "choosing"}]
    /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
    /\ vprop \in [1..N -> Values]
    /\ vpropstar \in [1..N -> Values]
    /\ vdec \in [1..N -> Values \cup {Bottom}]
    /\ crashed \in 0..N
    /\ msgs \in SUBSET [phase: MsgPhases, val: Values,
                        est: Values \cup {Bottom}, snd: 1..N]
    /\ recv \in [1..N -> SUBSET [phase: MsgPhases, val: Values,
                                 est: Values \cup {Bottom}, snd: 1..N]]

Init ==
    /\ loc = [n \in 1..N |-> "broad1"]
    /\ view = [n \in 1..N |-> [m \in 1..N |-> Bottom]]
    /\ vprop = [n \in 1..N |-> CHOOSE v \in Values : TRUE]
    /\ vpropstar = [n \in 1..N |-> Bottom]
    /\ vdec = [n \in 1..N |-> Bottom]
    /\ crashed = 0
    /\ msgs = {}
    /\ recv = [n \in 1..N |-> {}]

BroadcastPhase1(n) ==
    /\ loc[n] = "broad1"
    /\ msgs' = msgs \cup {[phase |-> "ph1", val |-> vprop[n],
                           est |-> Bottom, snd |-> n]}
    /\ loc' = [loc EXCEPT ![n] = "ph1wait"]
    /\ UNCHANGED <<view, vprop, vpropstar, vdec, crashed, recv>>

ReceivePhase1(n, m) ==
    /\ loc[n] = "ph1wait"
    /\ [phase |-> "ph1", val |-> vprop[m], est |-> Bottom, snd |-> m]
         \in msgs
    /\ [phase |-> "ph1", val |-> vprop[m], est |-> Bottom, snd |-> m]
         \notin recv[n]
    /\ view' = [view EXCEPT ![n][m] = vprop[m]]
    /\ recv' = [recv EXCEPT ![n] = recv[n] \cup
                   {[phase |-> "ph1", val |-> vprop[m], est |-> Bottom, snd |-> m]}]
    /\ UNCHANGED <<loc, vprop, vpropstar, vdec, crashed, msgs>>

TransitionPhase1(n) ==
    /\ loc[n] = "ph1wait"
    /\ Cardinality({m \in 1..N : [phase |-> "ph1", val |-> vprop[m],
                                   est |-> Bottom, snd |-> m] \in recv[n]})
         >= N - T
    /\ vpropstar' = [vpropstar EXCEPT ![n] =
                         CHOOSE v \in Values :
                             \A m \in 1..N : view[n][m] # Bottom => v >= view[n][m]]
    /\ loc' = [loc EXCEPT ![n] = "broad2"]
    /\ UNCHANGED <<view, vprop, vdec, crashed, msgs, recv>>

BroadcastPhase2(n) ==
    /\ loc[n] = "broad2"
    /\ msgs' = msgs \cup {[phase |-> "ph2", val |-> vprop[n],
                           est |-> vpropstar[n], snd |-> n]}
    /\ loc' = [loc EXCEPT ![n] = "ph2wait"]
    /\ UNCHANGED <<view, vprop, vpropstar, vdec, crashed, recv>>

ReceivePhase2(n, m) ==
    /\ loc[n] = "ph2wait"
    /\ [phase |-> "ph2", val |-> vprop[m], est |-> vpropstar[m], snd |-> m]
         \in msgs
    /\ [phase |-> "ph2", val |-> vprop[m], est |-> vpropstar[m], snd |-> m]
         \notin recv[n]
    /\ view' = [view EXCEPT ![n][m] = vpropstar[m]]
    /\ recv' = [recv EXCEPT ![n] = recv[n] \cup
                   {[phase |-> "ph2", val |-> vprop[m], est |-> vpropstar[m],
                     snd |-> m]}]
    /\ UNCHANGED <<loc, vprop, vpropstar, vdec, crashed, msgs>>

DecideOnEstimate(n) ==
    /\ loc[n] = "ph2wait"
    /\ \E e \in Values :
         /\ Cardinality({m \in 1..N : [phase |-> "ph2", val |-> vprop[m],
                                        est |-> e, snd |-> m] \in recv[n]})
              >= N - T
         /\ vdec' = [vdec EXCEPT ![n] = e]
    /\ loc' = [loc EXCEPT ![n] = "done"]
    /\ UNCHANGED <<view, vprop, vpropstar, crashed, msgs, recv>>

MoveToChoosing(n) ==
    /\ loc[n] = "ph2wait"
    /\ \A e \in Values :
         Cardinality({m \in 1..N : [phase |-> "ph2", val |-> vprop[m],
                                    est |-> e, snd |-> m] \in recv[n]})
             < N - T
    /\ \A m \in 1..N :
         [phase |-> "ph2", val |-> vprop[m], est |-> vpropstar[m], snd |-> m]
              \in recv[n]
    /\ loc' = [loc EXCEPT ![n] = "choosing"]
    /\ UNCHANGED <<view, vprop, vpropstar, vdec, crashed, msgs, recv>>

DeterministicChoose(n) ==
    /\ loc[n] = "choosing"
    /\ \E v \in Values :
         /\ \A m \in 1..N : view[n][m] # Bottom => v >= view[n][m]
         /\ vdec' = [vdec EXCEPT ![n] = v]
    /\ loc' = [loc EXCEPT ![n] = "done"]
    /\ UNCHANGED <<view, vprop, vpropstar, crashed, msgs, recv>>

Crash(n) ==
    /\ loc[n] \notin {"crashed", "done"}
    /\ crashed < F
    /\ loc' = [loc EXCEPT ![n] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, vprop, vpropstar, vdec, msgs, recv>>

Next ==
    \/ \E n \in 1..N : BroadcastPhase1(n) \/ BroadcastPhase2(n)
    \/ \E n \in 1..N, m \in 1..N : ReceivePhase1(n, m) \/ ReceivePhase2(n, m)
    \/ \E n \in 1..N : TransitionPhase1(n) \/ DecideOnEstimate(n)
                        \/ MoveToChoosing(n) \/ DeterministicChoose(n) \/ Crash(n)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E n \in 1..N, m \in 1..N : ReceivePhase1(n, m))
        /\ WF_vars(\E n \in 1..N : TransitionPhase1(n))
        /\ WF_vars(\E n \in 1..N, m \in 1..N : ReceivePhase2(n, m))
        /\ WF_vars(\E n \in 1..N : DecideOnEstimate(n))
        /\ WF_vars(\E n \in 1..N : DeterministicChoose(n))

Validity == \A n \in 1..N : vdec[n] # Bottom => \E m \in 1..N : vdec[n] = vprop[m]

Agreement == \A n, k \in 1..N : (vdec[n] # Bottom /\ vdec[k] # Bottom) => vdec[n] = vdec[k]

Termination == <>(\A n \in 1..N : loc[n] \in {"done", "crashed"})

ConditionC1 ==
    \A n \in 1..N :
        /\ loc[n] \in {"done", "crashed"}
        /\ vdec[n] # Bottom
    /\ Cardinality({m \in 1..N : vprop[m] = CHOOSE w \in Values :
                        \A o \in Values : (\A q \in 1..N : vprop[q] = w) => o <= w})
         >= F + 1

====