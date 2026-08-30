---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

None == 0
Locations == {"phase1", "wait1", "phase2", "wait2", "done", "crashed", "choose"}
MsgKinds == {"phase1", "phase2"}

VARIABLES loc, view, propose, estimate, decided, crashedCount, sent, received

vars == <<loc, view, propose, estimate, decided, crashedCount, sent, received>>

ViewSet(i) == { view[i][j] : j \in 1..N } \ {Bottom}
SeenEst(i, v) == { m \in received[i] : m.kind = "phase2" /\ m.estimate = v }

RECURSIVE MaxVal(_)
MaxVal(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN IF \E y \in S : y > x THEN MaxVal(S \ {x}) \cup {x} ELSE {x}

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {0}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..N
  /\ sent \subseteq [kind: MsgKinds, val: Values, from: 1..N, estimate: Values \cup {0}]
  /\ received \in [1..N -> SUBSET [kind: MsgKinds, val: Values, from: 1..N,
                          estimate: Values \cup {0}]]

Init ==
  /\ loc = [i \in 1..N |-> "phase1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> 0]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

BroadcastPhase1(i) ==
  /\ loc[i] = "phase1"
  /\ sent' = sent \cup {[kind |-> "phase1", val |-> propose[i], from |-> i, estimate |-> 0]}
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashedCount, received>>

ReceivePhase1(i, m) ==
  /\ loc[i] = "wait1"
  /\ m.kind = "phase1"
  /\ m \notin received[i]
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = received[i] \cup {m}]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashedCount, sent>>

Prepare(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality({ m \in received[i] : m.kind = "phase1" }) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE x \in MaxVal(ViewSet(i)) : TRUE]
  /\ loc' = "phase2"
  /\ UNCHANGED <<view, propose, decided, crashedCount, sent, received>>

BroadcastPhase2(i) ==
  /\ loc[i] = "phase2"
  /\ sent' = sent \cup {[kind |-> "phase2", val |-> propose[i], from |-> i,
                         estimate |-> estimate[i]]}
  /\ loc' = "wait2"
  /\ UNCHANGED <<view, propose, estimate, decided, crashedCount, received>>

ReceivePhase2(i, m) ==
  /\ loc[i] = "wait2"
  /\ m.kind = "phase2"
  /\ m \notin received[i]
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = received[i] \cup {m}]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashedCount, sent>>

DecideFromQuorum(i) ==
  /\ loc[i] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality(SeenEst(i, v)) >= N - T
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = "done"
  /\ UNCHANGED <<view, propose, estimate, crashedCount, sent, received>>

ChooseAny(i) ==
  /\ loc[i] = "wait2"
  /\ Cardinality({ m \in received[i] : m.kind = "phase2" }) = N
  /\ \E v \in Values :
       /\ v \in { view[i][j] : j \in 1..N }
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = "choose"
  /\ UNCHANGED <<view, propose, estimate, crashedCount, sent, received>>

Crash(i) ==
  /\ loc[i] # "crashed"
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<view, propose, estimate, decided, sent, received>>

Next ==
  \/ \E i \in 1..N : BroadcastPhase1(i)
  \/ \E i \in 1..N, m \in sent : ReceivePhase1(i, m)
  \/ \E i \in 1..N : Prepare(i)
  \/ \E i \in 1..N : BroadcastPhase2(i)
  \/ \E i \in 1..N, m \in sent : ReceivePhase2(i, m)
  \/ \E i \in 1..N : DecideFromQuorum(i)
  \/ \E i \in 1..N : ChooseAny(i)
  \/ \E i \in 1..N : Crash(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A i \in 1..N :
       /\ WF_vars(\E m \in sent : ReceivePhase1(i, m))
       /\ WF_vars(Prepare(i))
       /\ WF_vars(\E m \in sent : ReceivePhase2(i, m))
       /\ WF_vars(DecideFromQuorum(i))
       /\ WF_vars(ChooseAny(i))
       /\ WF_vars(Crash(i))

Validity == \A i \in 1..N : decided[i] # Bottom => decided[i] \in { propose[j] : j \in 1..N }

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed", "choose"})

ConditionC1 ==
  \A i \in 1..N, j \in 1..N : (i # j /\ loc[j] = "crashed") =>
    (propose[i] = (CHOOSE x \in Values : \A y \in Values : y <= x) /\ loc[i] \in {"done", "choose"})
====