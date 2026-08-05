---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, view, proposed, estimate, decided, crashes, sent, received
vars == <<pc, view, proposed, estimate, decided, crashes, sent, received>>

TypeOK ==
  /\ pc \in [1..N -> {"phase1", "wait1", "prepare", "phase2", "wait2", "done", "crash", "choose"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashes \in 0..F
  /\ sent \subseteq [type: {"phase1", "phase2"}, val: Values, src: 1..N, est: Values \cup {Bottom}]
  /\ received \in [1..N -> SUBSET [type: {"phase1", "phase2"}, val: Values, src: 1..N]]

Init ==
  /\ pc = [i \in 1..N |-> "phase1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashes = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

OnPath(i) == IF pc[i] = "crash" THEN {} ELSE {i}

BroadcastPhase1(i) ==
  /\ pc[i] = "phase1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposed[i], src |-> i, est |-> Bottom]}
  /\ pc' = [pc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, received>>

RecvPhase1(i, m) ==
  /\ pc[i] \in {"wait1"}
  /\ m.type = "phase1"
  /\ m.src \in OnPath(i)
  /\ m \notin received[i]
  /\ view' = [view EXCEPT ![i][m.src] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<pc, proposed, estimate, decided, crashes, sent>>

Prepare(i) ==
  /\ pc[i] = "wait1"
  /\ Cardinality({j \in 1..N : [type |-> "phase1", val |-> view[i][j], src |-> j] \in received[i]}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = CHOOSE m \in {view[i][j] : j \in 1..N} : \A n \in 1..N : view[i][n] <= m]
  /\ pc' = [pc EXCEPT ![i] = "phase2"]
  /\ UNCHANGED <<view, proposed, decided, crashes, sent, received>>

BroadcastPhase2(i) ==
  /\ pc[i] = "phase2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposed[i], src |-> i, est |-> estimate[i]]}
  /\ pc' = [pc EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, received>>

RecvPhase2(i, m) ==
  /\ pc[i] \in {"wait2"}
  /\ m.type = "phase2"
  /\ m.src \in OnPath(i)
  /\ m \notin received[i]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<pc, view, proposed, estimate, decided, crashes, sent>>

Decide(i) ==
  /\ pc[i] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({m \in received[i] : m.type = "phase2" /\ m.est = v}) >= N - T
       /\ decided[i] = Bottom
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashes, sent, received>>

Choose(i) ==
  /\ pc[i] = "wait2"
  /\ Cardinality({m \in received[i] : m.type = "phase2"}) = N
  /\ decided[i] = Bottom
  /\ \E v \in Values :
       /\ \A n \in 1..N : view[i][n] # Bottom => view[i][n] <= v
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ pc' = [pc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, proposed, estimate, crashes, sent, received>>

DecideChosen(i) ==
  /\ pc[i] = "choose"
  /\ decided[i] # Bottom
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, sent, received>>

Crash(i) ==
  /\ crashes < F
  /\ crashes' = crashes + 1
  /\ pc' = [pc EXCEPT ![i] = "crash"]
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, received>>

Next ==
  \/ \E i \in 1..N : BroadcastPhase1(i)
  \/ \E i \in 1..N, m \in sent : RecvPhase1(i, m)
  \/ \E i \in 1..N : Prepare(i)
  \/ \E i \in 1..N : BroadcastPhase2(i)
  \/ \E i \in 1..N, m \in sent : RecvPhase2(i, m)
  \/ \E i \in 1..N : Decide(i)
  \/ \E i \in 1..N : Choose(i)
  \/ \E i \in 1..N : DecideChosen(i)
  \/ \E i \in 1..N : Crash(i)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(Decide(1))
  /\ WF_vars(Decide(2))
  /\ WF_vars(DecideChosen(1))
  /\ WF_vars(DecideChosen(2))
  /\ WF_vars(Choose(1))
  /\ WF_vars(Choose(2))

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : decided[i] = proposed[j]

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination == <>(\A i \in 1..N : pc[i] \in {"crash", "done"})

ConditionC1 == (\A i \in 1..N : pc[i] = "phase1") => (\A i \in 1..N : pc[i] = "phase1") /\ (\E i \in 1..N : decided[i] = Bottom /\ \A j \in 1..N : decided[j] = Bottom)

====