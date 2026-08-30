---------------------------- MODULE cbc_max ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposed, estimated, decided, crashed, sent, received

vars == <<loc, view, proposed, estimated, decided, crashed, sent, received>>

Phases == {"broadcastPhase1", "waitPhase1", "prepare", "broadcastPhase2",
           "waitPhase2", "done", "crashed", "choosing"}

Messages == [type: {"phase1", "phase2"}, val: Values \cup {Bottom},
             est: Values \cup {Bottom}, from: 0 .. N - 1]

RECURSIVE MaxVal(_)
MaxVal(S) ==
    IF S = {} THEN Bottom
    ELSE LET x == CHOOSE y \in S : TRUE IN
         IF x = Bottom THEN MaxVal(S \ {x})
         ELSE IF \E z \in S \ {x} : z # Bottom /\ z > x
              THEN MaxVal(S \ {x})
              ELSE x

TypeOK ==
    /\ loc \in [0 .. N - 1 -> Phases]
    /\ view \in [0 .. N - 1 -> [0 .. N - 1 -> Values \cup {Bottom}]]
    /\ proposed \in [0 .. N - 1 -> Values]
    /\ estimated \in [0 .. N - 1 -> Values \cup {Bottom}]
    /\ decided \in [0 .. N - 1 -> Values \cup {Bottom}]
    /\ crashed \in 0 .. N
    /\ sent \subseteq Messages
    /\ received \in [0 .. N - 1 -> SUBSET Messages]

Init ==
    /\ loc = [p \in 0 .. N - 1 |-> "broadcastPhase1"]
    /\ view = [p \in 0 .. N - 1 |-> [q \in 0 .. N - 1 |-> Bottom]]
    /\ \E f \in [0 .. N - 1 -> Values] : proposed = f
    /\ estimated = [p \in 0 .. N - 1 |-> Bottom]
    /\ decided = [p \in 0 .. N - 1 |-> Bottom]
    /\ crashed = 0
    /\ sent = {}
    /\ received = [p \in 0 .. N - 1 |-> {}]

BroadcastPhase1(p) ==
    /\ loc[p] = "broadcastPhase1"
    /\ sent' = sent \cup {[type |-> "phase1", val |-> proposed[p], est |-> Bottom, from |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "waitPhase1"]
    /\ UNCHANGED <<view, proposed, estimated, decided, crashed, received>>

ReceivePhase1(p, m) ==
    /\ loc[p] = "waitPhase1"
    /\ m \in received[p]
    /\ m.type = "phase1"
    /\ view' = [view EXCEPT ![p][m.from] = m.val]
    /\ UNCHANGED <<loc, proposed, estimated, decided, crashed, sent, received>>

MoveToPrepare(p) ==
    /\ loc[p] = "waitPhase1"
    /\ Cardinality({q \in 0 .. N - 1 : [type |-> "phase1", val |-> view[p][q], est |-> Bottom, from |-> q] \in received[p]}) >= N - T
    /\ estimated' = [estimated EXCEPT ![p] = MaxVal({view[p][q] : q \in 0 .. N - 1})]
    /\ loc' = [loc EXCEPT ![p] = "broadcastPhase2"]
    /\ UNCHANGED <<view, proposed, decided, crashed, sent, received>>

BroadcastPhase2(p) ==
    /\ loc[p] = "broadcastPhase2"
    /\ sent' = sent \cup {[type |-> "phase2", val |-> proposed[p], est |-> estimated[p], from |-> p]}
    /\ loc' = [loc EXCEPT ![p] = "waitPhase2"]
    /\ UNCHANGED <<view, proposed, estimated, decided, crashed, received>>

ReceivePhase2(p, m) ==
    /\ loc[p] = "waitPhase2"
    /\ m \in received[p]
    /\ m.type = "phase2"
    /\ view' = [view EXCEPT ![p][m.from] = m.est]
    /\ UNCHANGED <<loc, proposed, estimated, decided, crashed, sent, received>>

Decide(p) ==
    /\ loc[p] = "waitPhase2"
    /\ Cardinality({q \in 0 .. N - 1 :
           [type |-> "phase2", val |-> proposed[q], est |-> view[p][q], from |-> q]
           \in received[p] /\ view[p][q] # Bottom}) >= N - T
    /\ \E e \in Values :
         /\ \A q \in 0 .. N - 1 :
              ([type |-> "phase2", val |-> proposed[q], est |-> view[p][q], from |-> q]
               \in received[p] /\ view[p][q] # Bottom) => view[p][q] = e
         /\ decided' = [decided EXCEPT ![p] = e]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimated, crashed, sent, received>>

Choose(p) ==
    /\ loc[p] = "waitPhase2"
    /\ {q \in 0 .. N - 1 : [type |-> "phase2", val |-> proposed[q], est |-> view[p][q], from |-> q] \in received[p]} = (0 .. N - 1)
    /\ loc' = [loc EXCEPT ![p] = "choosing"]
    /\ UNCHANGED <<view, proposed, estimated, decided, crashed, sent, received>>

DecideChosen(p) ==
    /\ loc[p] = "choosing"
    /\ \E e \in Values : decided' = [decided EXCEPT ![p] = e]
    /\ loc' = [loc EXCEPT ![p] = "done"]
    /\ UNCHANGED <<view, proposed, estimated, crashed, sent, received>>

Crash(p) ==
    /\ crashed < F
    /\ loc[p] # "crashed"
    /\ loc' = [loc EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed + 1
    /\ UNCHANGED <<view, proposed, estimated, decided, sent, received>>

Deliver(p, m) ==
    /\ m \in sent
    /\ m.from # p
    /\ m \notin received[p]
    /\ received' = [received EXCEPT ![p] = @ \cup {m}]
    /\ UNCHANGED <<loc, view, proposed, estimated, decided, crashed, sent>>

Next ==
    \/ \E p \in 0 .. N - 1 : BroadcastPhase1(p)
    \/ \E p \in 0 .. N - 1, m \in Messages : ReceivePhase1(p, m)
    \/ \E p \in 0 .. N - 1 : MoveToPrepare(p)
    \/ \E p \in 0 .. N - 1 : BroadcastPhase2(p)
    \/ \E p \in 0 .. N - 1, m \in Messages : ReceivePhase2(p, m)
    \/ \E p \in 0 .. N - 1 : Decide(p)
    \/ \E p \in 0 .. N - 1 : Choose(p)
    \/ \E p \in 0 .. N - 1 : DecideChosen(p)
    \/ \E p \in 0 .. N - 1 : Crash(p)
    \/ \E p \in 0 .. N - 1, m \in Messages : Deliver(p, m)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in 0 .. N - 1 : WF_vars(\E m \in Messages : ReceivePhase1(p, m))
    /\ \A p \in 0 .. N - 1 : SF_vars(\E m \in Messages : ReceivePhase2(p, m))
    /\ \A p \in 0 .. N - 1 : WF_vars(DecideChosen(p))
    /\ WF_vars(\E p \in 0 .. N - 1 : Crash(p))
    /\ WF_vars(\E p \in 0 .. N - 1 : MoveToPrepare(p))
    /\ WF_vars(\E p \in 0 .. N - 1 : Decide(p))

Validity ==
    \A p \in 0 .. N - 1 : decided[p] # Bottom => \E q \in 0 .. N - 1 : proposed[q] = decided[p]

Agreement ==
    \A p, q \in 0 .. N - 1 :
        (decided[p] # Bottom /\ decided[q] # Bottom) => decided[p] = decided[q]

Termination ==
    <>(\A p \in 0 .. N - 1 : loc[p] \in {"crashed", "done"})

ConditionC1 ==
    \A v \in Values : (Cardinality({p \in 0 .. N - 1 : proposed[p] = v}) >= F + 1)
                        => Cardinality({p \in 0 .. N - 1 : loc[p] \in {"crashed", "done"}}) = N

ConditionalTermination == ConditionC1 ~> Termination

=========================================================================