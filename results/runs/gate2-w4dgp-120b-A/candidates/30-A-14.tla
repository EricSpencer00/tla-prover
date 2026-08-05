---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ T > 0
       /\ F \in Nat /\ F >= 0 /\ F <= T
       /\ 2 * T < N
       /\ Bottom \notin Values

VARIABLES loc, view, propose, estimate, decided, crashes, sent, received
vars == <<loc, view, propose, estimate, decided, crashes, sent, received>>

Phases == {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choose"}
MsgType == {"phase1", "phase2"}

InitView == [i \in 1..N |-> Bottom]

TypeOK ==
  /\ loc \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashes \in 0..N
  /\ sent \subseteq [type: MsgType, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N]
  /\ received \in [1..N -> SUBSET [type: MsgType, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N]]

Sendable ==
  { m \in [type: MsgType, val: Values \cup {Bottom}, est: Values \cup {Bottom}, from: 1..N] :
      /\ m.from >= 1 /\ m.from <= N
      /\ m.val \in Values \cup {Bottom}
      /\ m.est \in Values \cup {Bottom}
      /\ m.type \in MsgType }

Init ==
  /\ loc = [i \in 1..N |-> "bc1"]
  /\ view = [i \in 1..N |-> InitView]
  /\ propose \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decided = [i \in 1..N |-> Bottom]
  /\ crashes = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

\* Phase 1: each process broadcasts its proposed value.
Bcast1(i) ==
  /\ loc[i] = "bc1"
  /\ Sendable
  /\ \E m \in Sendable :
       /\ m.type = "phase1"
       /\ m.val = propose[i]
       /\ m.est = Bottom
       /\ m.from = i
       /\ sent' = sent \cup {m}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashes, received>>

\* Phase 1: a process receives a proposal and updates its local view.
Recv1(i) ==
  /\ loc[i] \in {"w1", "bc2", "w2", "choose"}
  /\ \E m \in sent :
       /\ m.type = "phase1"
       /\ m.val \in Values \cup {Bottom}
       /\ m.from \notin {x.from : x \in received[i]}
       /\ received' = [received EXCEPT ![i] = @ \cup {m}]
       /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ UNCHANGED <<loc, propose, estimate, decided, crashes, sent>>

\* Phase 1: when enough distinct proposals have been collected, the
\* process estimates the maximum of its view and moves to phase 2.
Estimate(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality({x.from : x \in received[i]}) >= (N - T)
  /\ LET maxv == CHOOSE y \in Values :
         /\ \A j \in 1..N : view[i][j] \in Values => view[i][j] <= y
         /\ \A z \in Values : (\A j \in 1..N : view[i][j] \in Values => view[i][j] <= z) => y <= z
     IN /\ estimate' = [estimate EXCEPT ![i] = maxv]
        /\ loc' = [loc EXCEPT ![i] = "bc2"]
  /\ UNCHANGED <<view, propose, decided, crashes, sent, received>>

\* Phase 2: each process broadcasts its proposed value together with its estimate.
Bcast2(i) ==
  /\ loc[i] = "bc2"
  /\ Sendable
  /\ \E m \in Sendable :
       /\ m.type = "phase2"
       /\ m.val = propose[i]
       /\ m.est = estimate[i]
       /\ m.from = i
       /\ sent' = sent \cup {m}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashes, received>>

\* Phase 2: a process receives proposals and decides once enough of them
\* carry the same estimated value (the N-T threshold is reached).
Decide(i) ==
  /\ loc[i] \in {"w2", "choose"}
  /\ \E v \in Values :
       /\ Cardinality({x \in received[i] : x.type = "phase2" /\ x.est = v}) >= (N - T)
       /\ decided' = [decided EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashes, sent, received>>

\* Phase 2: when the N-T threshold for any single estimate is not met
\* the process deterministically chooses some value it has seen.
Choose(i) ==
  /\ loc[i] = "choose"
  /\ \E v \in Values :
       /\ \E j \in 1..N : view[i][j] = v
       /\ decided' = [decided EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashes, sent, received>>

Crash(i) ==
  /\ crashes < F
  /\ loc[i] \notin {"crashed", "done"}
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<view, propose, estimate, decided, sent, received>>

Next ==
  \/ \E i \in 1..N : Bcast1(i) \/ Recv1(i) \/ Estimate(i) \/ Bcast2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..N : Recv1(i))
        /\ WF_vars(\E i \in 1..N : Bcast1(i))
        /\ WF_vars(\E i \in 1..N : Estimate(i))
        /\ WF_vars(\E i \in 1..N : Bcast2(i))
        /\ WF_vars(\E i \in 1..N : Decide(i))
        /\ WF_vars(\E i \in 1..N : Choose(i))

Validity ==
  /\ \A i \in 1..N : decided[i] # Bottom => \E j \in 1..N : propose[j] = decided[i]
  /\ \A i \in 1..N, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Agreement ==
  /\ \A i \in 1..N : decided[i] # Bottom => decided[i] \in Values
  /\ \A i, j \in 1..N : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

Termination ==
  \A i \in 1..N : (loc[i] = "crashed" \/ decided[i] # Bottom) ~> TRUE

ConditionC1 ==
  (Cardinality({i \in 1..N : propose[i] = CHOOSE x \in Values :
                     /\ \A j \in 1..N : propose[j] \in Values => propose[j] <= x
                     /\ \A y \in Values : (\A j \in 1..N : propose[j] \in Values => propose[j] <= y) => x <= y)}) >= (F + 1))
    ~> (\A i \in 1..N : loc[i] = "crashed" \/ decided[i] # Bottom)

====