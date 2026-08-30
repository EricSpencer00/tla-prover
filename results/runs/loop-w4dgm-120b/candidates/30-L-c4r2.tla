---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* 2T < N: bound on tolerated crash faults; F <= T: fault limit used by the
\* protocol; Bottom: the sentinel for "no value" in local views.
\* SAFETY: Validity (decided values were proposed) and Agreement (no two
\* processes decide differently). LIVENESS: eventual decision or crash, and
\* guaranteed termination under Condition C1 (enough max-value proposals).

VARIABLES pc, seen, proposal, estimate, decided, crashed, sent, recvd

Clients == 0..(N - 1)
Msgs == [kind: {"phase1", "phase2"}, val: Values \cup {Bottom}, sender: Clients,
         est: Values \cup {Bottom}]

MaxV(S) ==
  LET f[T \in SUBSET Values] ==
        IF T = {} THEN Bottom
        ELSE LET x == CHOOSE y \in T : TRUE
             IN IF \E y \in T : y > x THEN f[T \ {x}] \cup {x} ELSE T
  IN CHOOSE x \in f[S] : TRUE

MaxIn(a) == MaxV({a[i] : i \in Clients})

TypeOK ==
  /\ pc \in [Clients -> {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choosing"}]
  /\ seen \in [Clients -> [Clients -> Values \cup {Bottom}]]
  /\ proposal \in [Clients -> Values]
  /\ estimate \in [Clients -> Values \cup {Bottom}]
  /\ decided \in [Clients -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msgs
  /\ recvd \in [Clients -> SUBSET Msgs]

Init ==
  /\ pc = [i \in Clients |-> "bc1"]
  /\ seen = [i \in Clients |-> [j \in Clients |-> Bottom]]
  /\ proposal \in [Clients -> Values]
  /\ estimate = [i \in Clients |-> Bottom]
  /\ decided = [i \in Clients |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [i \in Clients |-> {}]

Broadcast1(i) ==
  /\ pc[i] = "bc1"
  /\ sent' = sent \cup {[kind |-> "phase1", val |-> proposal[i], sender |-> i, est |-> Bottom]}
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<seen, proposal, estimate, decided, crashed, recvd>>

Receive1(i, m) ==
  /\ pc[i] = "w1"
  /\ m.kind = "phase1"
  /\ m \notin recvd[i]
  /\ seen[i][m.sender] = Bottom
  /\ seen' = [seen EXCEPT ![i][m.sender] = m.val]
  /\ recvd' = [recvd EXCEPT ![i] = recvd[i] \cup {m}]
  /\ UNCHANGED <<pc, proposal, estimate, decided, crashed, sent>>

Prepare(i) ==
  /\ pc[i] = "w1"
  /\ Cardinality({j \in Clients : seen[i][j] # Bottom}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = MaxIn(seen[i])]
  /\ pc' = [pc EXCEPT ![i] = "bc2"]
  /\ UNCHANGED <<seen, proposal, decided, crashed, sent, recvd>>

Broadcast2(i) ==
  /\ pc[i] = "prep"
  /\ sent' = sent \cup {[kind |-> "phase2", val |-> proposal[i], sender |-> i,
                         est |-> estimate[i]]}
  /\ pc' = [pc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<seen, proposal, estimate, decided, crashed, recvd>>

Receive2(i, m) ==
  /\ pc[i] = "w2"
  /\ m.kind = "phase2"
  /\ m \notin recvd[i]
  /\ seen' = [seen EXCEPT ![i][m.sender] = m.val]
  /\ recvd' = [recvd EXCEPT ![i] = recvd[i] \cup {m}]
  /\ UNCHANGED <<pc, proposal, estimate, decided, crashed, sent>>

Decide(i) ==
  /\ pc[i] = "w2"
  /\ \E v \in Values :
        /\ Cardinality({m \in recvd[i] : m.kind = "phase2" /\ m.est = v})
             >= N - T
        /\ decided' = [decided EXCEPT ![i] = v]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<seen, proposal, estimate, crashed, sent, recvd>>

Choose(i) ==
  /\ pc[i] = "w2"
  /\ \A m \in recvd[i] : m.kind = "phase2"
  /\ Cardinality({m \in recvd[i] : m.kind = "phase2"}) = N
  /\ (\A v \in Values :
        Cardinality({m \in recvd[i] : m.kind = "phase2" /\ m.est = v}) < N - T)
  /\ \E v \in Values : \E j \in Clients :
        /\ seen[i][j] = v
        /\ decided' = [decided EXCEPT ![i] = v]
  /\ pc' = [pc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<seen, proposal, estimate, crashed, sent, recvd>>

Crash(i) ==
  /\ pc[i] \notin {"done", "crashed"}
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ pc' = [pc EXCEPT ![i] = "crashed"]
  /\ UNCHANGED <<seen, proposal, estimate, decided, sent, recvd>>

Next ==
  \/ \E i \in Clients :
        \/ Broadcast1(i) \/ Prepare(i) \/ Broadcast2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
        \/ \E m \in Msgs : Receive1(i, m) \/ Receive2(i, m)

Spec ==
  /\ Init /\ [][Next]_<<pc, seen, proposal, estimate, decided, crashed, sent, recvd>>
  /\ \A i \in Clients : WF_vars(Broadcast1(i)) /\ WF_vars(Receive1(i, [kind |-> "phase1", val |-> proposal[i], sender |-> i, est |-> Bottom]))
  /\ \A i \in Clients : WF_vars(Prepare(i)) /\ WF_vars(Broadcast2(i))
  /\ \A i \in Clients : WF_vars(Receive2(i, [kind |-> "phase2", val |-> proposal[i], sender |-> i, est |-> estimate[i]]))
  /\ \A i \in Clients : WF_vars(Decide(i)) /\ WF_vars(Choose(i))
  /\ WF_vars(\E i \in Clients : Crash(i))

Validity == \A i \in Clients : decided[i] # Bottom => \E j \in Clients : proposal[j] = decided[i]

Agreement == \A i, j \in Clients : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

C1 == Cardinality({i \in Clients : proposal[i] = MaxV(Values)}) >= F + 1

Termination == WF_vars(\E i \in Clients : Crash(i))

CTerm == C1 /\ Termination

====