---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ F \in Nat
       /\ 2 * T < N
       /\ F <= T
       /\ Bottom \notin Values

VARIABLES phase, view, prop, est, decision, crashCount, msgs, recvMsgs

vars == <<phase, view, prop, est, decision, crashCount, msgs, recvMsgs>>
phases == {"bc1", "wait1", "prep", "bc2", "wait2", "done", "crashed", "choose"}
Types ==
  /\ phase \in [1..N -> phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashCount \in 0..N
  /\ msgs \subseteq [type : {"p1", "p2"}, val : Values, sender : 1..N, est : Values \cup {Bottom}]
  /\ recvMsgs \in [1..N -> SUBSET msgs]

Init ==
  /\ phase = [i \in 1..N |-> "bc1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [i \in 1..N |-> CHOOSE v \in Values : TRUE]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashCount = 0
  /\ msgs = {}
  /\ recvMsgs = [i \in 1..N |-> {}]

Recv(i, m) ==
  /\ m \in msgs
  /\ m.type = IF phase[i] \in {"wait1", "prep"} THEN "p1" ELSE "p2"
  /\ m.sender \notin {x.sender : x \in recvMsgs[i]}
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] = recvMsgs[i] \cup {m}]
  /\ view' = [view EXCEPT ![i][m.sender] = m.val]
  /\ UNCHANGED <<phase, prop, est, decision, crashCount, msgs>>

BroadcastP1(i) ==
  /\ phase[i] = "bc1"
  /\ msgs' = msgs \cup {[type |-> "p1", val |-> prop[i], sender |-> i, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![i] = "wait1"]
  /\ UNCHANGED <<view, prop, est, decision, crashCount, recvMsgs>>

BroadcastP2(i) ==
  /\ phase[i] = "prep"
  /\ msgs' = msgs \cup {[type |-> "p2", val |-> prop[i], sender |-> i, est |-> est[i]]}
  /\ phase' = [phase EXCEPT ![i] = "wait2"]
  /\ UNCHANGED <<view, prop, est, decision, crashCount, recvMsgs>>

DoPrep(i) ==
  /\ phase[i] = "wait1"
  /\ Cardinality({x.sender : x \in recvMsgs[i]}) >= N - T
  /\ est' = [est EXCEPT ![i] = Max({view[i][j] : j \in 1..N})]
  /\ phase' = [phase EXCEPT ![i] = "prep"]
  /\ UNCHANGED <<view, prop, decision, crashCount, msgs, recvMsgs>>

Decide(i) ==
  /\ phase[i] = "wait2"
  /\ \E v \in Values :
       /\ Cardinality({x \in recvMsgs[i] : x.type = "p2" /\ x.est = v})
          >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashCount, msgs, recvMsgs>>

MoveChoose(i) ==
  /\ phase[i] = "wait2"
  /\ \A m \in recvMsgs[i] : m.type = "p2"
  /\ Cardinality(recvMsgs[i]) = N
  /\ phase' = [phase EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, est, decision, crashCount, msgs, recvMsgs>>

DoChoose(i) ==
  /\ phase[i] = "choose"
  /\ \E v \in Values :
       /\ v \in {view[i][j] : j \in 1..N}
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ phase' = [phase EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashCount, msgs, recvMsgs>>

Crash(i) ==
  /\ phase[i] \notin {"crashed", "done"}
  /\ crashCount < F
  /\ phase' = [phase EXCEPT ![i] = "crashed"]
  /\ crashCount' = crashCount + 1
  /\ UNCHANGED <<view, prop, est, decision, msgs, recvMsgs>>

Next ==
  \/ \E i \in 1..N : BroadcastP1(i)
  \/ \E i \in 1..N, m \in msgs : Recv(i, m)
  \/ \E i \in 1..N : DoPrep(i)
  \/ \E i \in 1..N : BroadcastP2(i)
  \/ \E i \in 1..N : Decide(i)
  \/ \E i \in 1..N : MoveChoose(i)
  \/ \E i \in 1..N : DoChoose(i)
  \/ \E i \in 1..N : Crash(i)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in msgs : Recv(i, m))
  /\ WF_vars(\E i \in 1..N : DoPrep(i))
  /\ WF_vars(\E i \in 1..N : Decide(i))
  /\ WF_vars(\E i \in 1..N : DoChoose(i))

TypeOK == Types

Validity ==
  \A i \in 1..N : decision[i] # Bottom => decision[i] \in {prop[j] : j \in 1..N}

Agreement ==
  \A i, j \in 1..N : /\ decision[i] # Bottom
                     /\ decision[j] # Bottom
                     => decision[i] = decision[j]

Terminate ==
  <>(\A i \in 1..N : phase[i] \in {"done", "crashed"})

C1Terminate ==
  ((Cardinality({i \in 1..N : prop[i] = Max(Values)}) >= F + 1) =>
     <>(\A i \in 1..N : phase[i] \in {"done", "crashed"}))

====