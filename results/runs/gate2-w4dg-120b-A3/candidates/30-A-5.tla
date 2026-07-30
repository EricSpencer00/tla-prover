---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, T, F, Values, Bottom

Locations == {"broadcast-1", "waiting-1", "prepare", "broadcast-2",
              "waiting-2", "finished", "crashed", "choose"}
MsgKinds == {"phase-1", "phase-2"}
Phases == {"phase-1", "phase-2"}

VARIABLES loc, matrix, proposal, estimate, decision, crashedCount,
         sent, received

vars == <<loc, matrix, proposal, estimate, decision, crashedCount,
          sent, received>>

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ matrix \in [1..N -> [1..N -> Values \union {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \union {Bottom}]
  /\ decision \in [1..N -> Values \union {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq [kind: MsgKinds, val: Values,
                     src: 1..N, e: Values \union {Bottom}]
  /\ received \in [1..N -> SUBSET [kind: MsgKinds, val: Values,
                                   src: 1..N, e: Values \union {Bottom}]]

Init ==
  /\ loc = [i \in 1..N |-> "broadcast-1"]
  /\ matrix = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

ValidReceiver(k, i) == IF loc[i] = "waiting-1" THEN k.kind = "phase-1"
                       ELSE k.kind = "phase-2"

BroadcastPhase1(i) ==
  /\ loc[i] = "broadcast-1"
  /\ sent' = sent \union {[kind |-> "phase-1", val |-> proposal[i],
                           src |-> i, e |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "waiting-1"]
  /\ UNCHANGED <<matrix, proposal, estimate, decision,
                 crashedCount, received>>

Receive(i, k) ==
  /\ loc[i] \in {"waiting-1", "waiting-2"}
  /\ ValidReceiver(k, i)
  /\ k \notin received[i]
  /\ matrix' = [matrix EXCEPT ![i][k.src] = k.val]
  /\ received' = [received EXCEPT ![i] = @ \union {k}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashedCount, sent>>

ComputeEstimate(i) ==
  /\ loc[i] = "waiting-1"
  /\ Cardinality({k \in received[i] : k.kind = "phase-1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE x \in Values :
                    \A j \in 1..N : matrix[i][j] # Bottom => matrix[i][j] <= x]
  /\ loc' = [loc EXCEPT ![i] = "broadcast-2"]
  /\ UNCHANGED <<matrix, proposal, decision, crashedCount, sent, received>>

BroadcastPhase2(i) ==
  /\ loc[i] = "broadcast-2"
  /\ sent' = sent \union {[kind |-> "phase-2", val |-> proposal[i],
                           src |-> i, e |-> estimate[i]}]
  /\ loc' = [loc EXCEPT ![i] = "waiting-2"]
  /\ UNCHANGED <<matrix, proposal, estimate, decision,
                 crashedCount, received>>

Decide(i, v) ==
  /\ loc[i] = "waiting-2"
  /\ Cardinality({k \in received[i] : k.kind = "phase-2" /\ k.e = v}) >= N - T
  /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "finished"]
  /\ UNCHANGED <<matrix, proposal, estimate, crashedCount, sent, received>>

EnterChoosing(i) ==
  /\ loc[i] = "waiting-2"
  /\ \A v \in Values : Cardinality({k \in received[i] : k.kind = "phase-2" /\ k.e = v}) < N - T
  /\ \A k \in received[i] : k.kind = "phase-2"
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<matrix, proposal, estimate, decision,
                 crashedCount, sent, received>>

Choose(i, v) ==
  /\ loc[i] = "choose"
  /\ \E j \in 1..N : matrix[i][j] = v
  /\ proposal[i] = v \/ \E j \in 1..N : matrix[i][j] = v
  /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "finished"]
  /\ UNCHANGED <<matrix, proposal, estimate, crashedCount, sent, received>>

Crash(i) ==
  /\ loc[i] \notin {"crashed", "finished"}
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<matrix, proposal, estimate, decision, sent, received>>

Next ==
  \/ \E i \in 1..N : BroadcastPhase1(i) \/ ComputeEstimate(i) \/ BroadcastPhase2(i) \/ EnterChoosing(i) \/ Crash(i)
  \/ \E i \in 1..N, k \in MsgKinds \times Values \times (1..N) \times (Values \union {Bottom}) :
        Receive(i, [kind |-> k[1], val |-> k[2], src |-> k[3], e |-> k[4]])
  \/ \E i \in 1..N, v \in Values : Decide(i, v) \/ Choose(i, v)

Spec == Init /\ [][Next]_vars
        /\ (\A k \in MsgKinds \times Values \times (1..N) \times (Values \union {Bottom}) :
              WF_vars(\E i \in 1..N : Receive(i, [kind |-> k[1], val |-> k[2], src |-> k[3], e |-> k[4]]))
              /\ WF_vars(\E i \in 1..N : Decide(i, k[2]))
              /\ WF_vars(\E i \in 1..N : Choose(i, k[2])))

Validity == \A i \in 1..N : decision[i] # Bottom => decision[i] \in Values

Agreement == \A i, j \in 1..N : decision[i] # Bottom /\ decision[j] # Bottom => decision[i] = decision[j]

Termination ==
  <>(\A i \in 1..N : loc[i] \in {"finished", "crashed"})

ConditionC1 ==
  \A v \in Values : v = CHOOSE x \in Values : \A y \in Values : y <= x
    => Cardinality({i \in 1..N : proposal[i] = v}) >= F + 1 => Termination

Properties == Termination /\ ConditionC1

====