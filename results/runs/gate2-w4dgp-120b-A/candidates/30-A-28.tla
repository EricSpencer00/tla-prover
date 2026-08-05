---- MODULE cbc_max ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ 2 * T < N
       /\ F \in Nat /\ F <= T
       /\ Values \subseteq Nat
       /\ Bottom \notin Values

VARIABLES loc, view, proposed, estimate, decided, crashes, sent, received
vars == <<loc, view, proposed, estimate, decided, crashes, sent, received>>

Locs == {"broadcast1", "wait1", "prepare", "broadcast2", "wait2",
         "done", "crashed", "choose"}
Msgs == [type: {"phase1", "phase2"}, val: Values \cup {Bottom},
         from: 1..N, est: Values \cup {Bottom}]

TypeOK ==
  /\ loc \in [1..N -> Locs]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashes \in 0..F
  /\ sent \subseteq Msgs
  /\ received \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [i \in 1..N |-> "broadcast1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashes = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

Broadcast1(i) ==
  /\ loc[i] = "broadcast1"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposed[i],
                         from |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, received>>

Receive1(i, m) ==
  /\ loc[i] = "wait1"
  /\ m.type = "phase1"
  /\ m \notin received[i]
  /\ m.from \notin {r.from : r \in received[i]}
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashes, sent>>

ComputeEstimate(i) ==
  /\ loc[i] = "wait1"
  /\ Cardinality({r.from : r \in received[i]}) >= N - T
  /\ \E v \in Values :
       /\ \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= v
       /\ estimate' = [estimate EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "broadcast2"]
  /\ UNCHANGED <<view, proposed, decided, crashes, sent, received>>

Broadcast2(i) ==
  /\ loc[i] = "broadcast2"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposed[i],
                         from |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, received>>

Receive2(i, m) ==
  /\ loc[i] = "wait2"
  /\ m.type = "phase2"
  /\ m \notin received[i]
  /\ m.from \notin {r.from : r \in received[i]}
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashes, sent>>

DecideMajority(i) ==
  /\ loc[i] = "wait2"
  /\ \E e \in Values :
       /\ Cardinality({m.from : m \in received[i]
                        /\ m.type = "phase2" /\ m.est = e}) >= N - T
       /\ decided' = [decided EXCEPT ![i] = e]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashes, sent, received>>

Choose(i) ==
  /\ loc[i] = "wait2"
  /\ {m.from : m \in received[i] /\ m.type = "phase2"} = 1..N
  /\ \A e \in Values :
        Cardinality({m.from : m \in received[i] /\ m.type = "phase2" /\ m.est = e}) < N - T
  /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, sent, received>>

DeterministicPick(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values :
       /\ \A j \in 1..N : view[i][j] # Bottom => view[i][j] <= v
       /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashes, sent, received>>

Crash(i) ==
  /\ loc[i] \notin {"done", "crashed"}
  /\ crashes < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, received>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ ComputeEstimate(i) \/ Broadcast2(i)
                     \/ DecideMajority(i) \/ Choose(i) \/ DeterministicPick(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in Msgs : Receive1(i, m) \/ Receive2(i, m)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..N : Broadcast1(i))
        /\ WF_vars(\E i \in 1..N, m \in Msgs : Receive1(i, m))
        /\ WF_vars(\E i \in 1..N : ComputeEstimate(i))
        /\ WF_vars(\E i \in 1..N : Broadcast2(i))
        /\ WF_vars(\E i \in 1..N, m \in Msgs : Receive2(i, m))
        /\ WF_vars(\E i \in 1..N : DecideMajority(i))
        /\ WF_vars(\E i \in 1..N : Choose(i))
        /\ WF_vars(\E i \in 1..N : DeterministicPick(i))

Validity == \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : decided[i] = proposed[j]

Agreement == \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination ==
  \A i \in 1..N : (loc[i] = "done" \/ loc[i] = "crashed")
      WF_vars(\E i \in 1..N : loc[i] = "broadcast1" \/ loc[i] = "wait1")
      WF_vars(\E i \in 1..N : loc[i] = "wait2")
      WF_vars(\E i \in 1..N : loc[i] = "broadcast2")
      WF_vars(\E i \in 1..N : loc[i] = "wait1")
      WF_vars(\E i \in 1..N : loc[i] = "prepare")
      WF_vars(\E i \in 1..N : loc[i] = "choose")

ConditionC1 ==
  (Cardinality({i \in 1..N : proposed[i] = Max(Values)}) >= F + 1) ~>
    (\A i \in 1..N : loc[i] = "done" \/ loc[i] = "crashed")
      WF_vars(\E i \in 1..N : loc[i] = "broadcast1" \/ loc[i] = "wait1")
      WF_vars(\E i \in 1..N : loc[i] = "wait2")
      WF_vars(\E i \in 1..N : loc[i] = "broadcast2")
      WF_vars(\E i \in 1..N : loc[i] = "wait1" \/ loc[i] = "prepare")
      WF_vars(\E i \in 1..N : loc[i] = "choose")

====