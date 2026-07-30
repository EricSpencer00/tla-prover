---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* The protocol's actions (Init, Broadcast1, Recv1, Compute, Broadcast2,
\* Decide, Choose) are user-level; the rest are for fairness only.
\* The underlying behavior is a truly asynchronous message passing system
\* with bounded buffering: a message may be delivered in any order.
\* Fairness guarantees everything eventually happens, which is what the
\* spec assumes (the spec's liveness guarantees would not hold otherwise).

VARIABLES phase, view, proposal, estimate, decision, crashed, sent, recvd
vars == << phase, view, proposal, estimate, decision, crashed, sent, recvd >>

Location == { "bcast1", "wait1", "prepare", "bcast2", "wait2", "done", "crashed", "choose" }
MessageType == { "phase1", "phase2" }
Message == [ type : MessageType, val : Values \cup {Bottom}, from : 0 .. (N - 1), est : Values \cup {Bottom} ]
Seen(id) == { m.from : m \in recvd[id] }

Init ==
  /\ phase = [ i \in 0 .. (N - 1) |-> "bcast1" ]
  /\ view = [ i \in 0 .. (N - 1), j \in 0 .. (N - 1) |-> Bottom ]
  /\ proposal = [ i \in 0 .. (N - 1) |-> CHOOSE v \in Values : TRUE ]
  /\ estimate = [ i \in 0 .. (N - 1) |-> Bottom ]
  /\ decision = [ i \in 0 .. (N - 1) |-> Bottom ]
  /\ crashed = 0
  /\ sent = {}
  /\ recvd = [ i \in 0 .. (N - 1) |-> {} ]

Broadcast1(id) ==
  /\ phase[id] = "bcast1"
  /\ phase' = [ phase EXCEPT ![id] = "wait1" ]
  /\ sent' = sent \cup { [ type |-> "phase1", val |-> proposal[id], from |-> id, est |-> Bottom ] }
  /\ UNCHANGED << view, proposal, estimate, decision, crashed, recvd >>

Recv1(id, m) ==
  /\ phase[id] = "wait1"
  /\ m \in sent
  /\ m.type = "phase1"
  /\ view' = [ view EXCEPT ![id, m.from] = m.val ]
  /\ recvd' = [ recvd EXCEPT ![id] = recvd[id] \cup { m } ]
  /\ UNCHANGED << phase, proposal, estimate, decision, crashed, sent >>

Compute(id) ==
  /\ phase[id] = "wait1"
  /\ Cardinality(recvd[id]) >= (N - T)
  /\ \A j \in 0 .. (N - 1) : view[id, j] # Bottom
  /\ estimate' = [ estimate EXCEPT ![id] = Max({ view[id, j] : j \in 0 .. (N - 1) }) ]
  /\ phase' = [ phase EXCEPT ![id] = "bcast2" ]
  /\ UNCHANGED << view, proposal, decision, crashed, sent, recvd >>

Broadcast2(id) ==
  /\ phase[id] = "bcast2"
  /\ phase' = [ phase EXCEPT ![id] = "wait2" ]
  /\ sent' = sent \cup { [ type |-> "phase2", val |-> proposal[id], from |-> id, est |-> estimate[id] ] }
  /\ UNCHANGED << view, proposal, estimate, decision, crashed, recvd >>

Decide(id, v) ==
  /\ phase[id] = "wait2"
  /\ \E S \in SUBSET recvd[id] :
       /\ Cardinality(S) >= (N - T)
       /\ \A m \in S : m.est = v
  /\ decision' = [ decision EXCEPT ![id] = v ]
  /\ phase' = [ phase EXCEPT ![id] = "done" ]
  /\ UNCHANGED << view, proposal, estimate, crashed, sent, recvd >>

Choose(id, v) ==
  /\ phase[id] = "wait2"
  /\ Cardinality(recvd[id]) = N
  /\ v \in { view[id, j] : j \in 0 .. (N - 1) }
  /\ decision' = [ decision EXCEPT ![id] = v ]
  /\ phase' = [ phase EXCEPT ![id] = "choose" ]
  /\ UNCHANGED << view, proposal, estimate, crashed, sent, recvd >>

Crash(id) ==
  /\ phase[id] \notin { "crashed", "done", "choose" }
  /\ crashed < F
  /\ phase' = [ phase EXCEPT ![id] = "crashed" ]
  /\ crashed' = crashed + 1
  /\ UNCHANGED << view, proposal, estimate, decision, sent, recvd >>

Next ==
  \/ \E id \in 0 .. (N - 1) : Broadcast1(id) \/ Compute(id) \/ Broadcast2(id) \/ Crash(id)
  \/ \E id \in 0 .. (N - 1), m \in Message : Recv1(id, m)
  \/ \E id \in 0 .. (N - 1), v \in Values : Decide(id, v) \/ Choose(id, v)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E id \in 0 .. (N - 1) : Broadcast1(id))
  /\ WF_vars(\E id \in 0 .. (N - 1), m \in Message : Recv1(id, m))
  /\ WF_vars(\E id \in 0 .. (N - 1) : Compute(id))
  /\ WF_vars(\E id \in 0 .. (N - 1) : Broadcast2(id))
  /\ WF_vars(\E id \in 0 .. (N - 1), v \in Values : Decide(id, v))
  /\ WF_vars(\E id \in 0 .. (N - 1), v \in Values : Choose(id, v))
  /\ WF_vars(\E id \in 0 .. (N - 1) : Crash(id))

TypeOK ==
  /\ phase \in [ 0 .. (N - 1) -> Location ]
  /\ view \in [ 0 .. (N - 1), 0 .. (N - 1) -> Values \cup {Bottom} ]
  /\ proposal \in [ 0 .. (N - 1) -> Values ]
  /\ estimate \in [ 0 .. (N - 1) -> Values \cup {Bottom} ]
  /\ decision \in [ 0 .. (N - 1) -> Values \cup {Bottom} ]
  /\ crashed \in 0 .. N
  /\ recvd \in [ 0 .. (N - 1) -> SUBSET Message ]

Validity == \A i \in 0 .. (N - 1) : decision[i] # Bottom => decision[i] \in Values
Agreement == \A i, j \in 0 .. (N - 1) : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination == <>(\A i \in 0 .. (N - 1) : phase[i] \in { "crashed", "done", "choose" })
ConditionC1 == \A i \in 0 .. (N - 1) : phase[i] = "done" =>
                (\E S \in SUBSET 0 .. (N - 1) : Cardinality(S) >= (F + 1) /\
                     \A k \in S : proposal[k] = Max(Values))

Properties == Termination /\ ConditionC1

====