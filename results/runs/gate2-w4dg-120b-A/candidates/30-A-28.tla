---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Phase labels: 1 for broadcast phase 1, 2 for broadcast phase 2.
\* The term "waiting" follows the paper's description of the phase.
\* The location set is fully enumerated so the model cannot silently drop a
\* location that an action later assumes is reachable.
\* Below that set is the group of disallowed locations.
\* Phase-2 messages carry the sender's estimate; phase-1 messages do not.
\* The local view is an N-by-N matrix: view[i][j] is what process i holds about j.
\* To keep the spec safe, every compared value is distinct from Bottom, and the
\* same holds for each decision once made.

Locations ==
  { "broadcast1", "waiting1", "preparing",
    "broadcast2", "waiting2", "done", "crashed", "choosing" }

MessageType == { "phase1", "phase2" }
Msg == [type: MessageType, val: Values \cup {Bottom}, snd: 1..N, est: Values \cup {Bottom}]

VARIABLES loc, view, proposal, estimate, decision, crashed, sent, received

vars == <<loc, view, proposal, estimate, decision, crashed, sent, received>>

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msg
  /\ received \in [1..N -> SUBSET Msg]

Max2Of(S) == LET a == CHOOSE x \in S : TRUE
                 b == CHOOSE y \in S \ {a} : TRUE
             IN IF a > b THEN a ELSE b

Init ==
  /\ loc = [i \in 1..N |-> "broadcast1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

\* Broadcast a phase-1 message carrying only the proposed value.
Broadcast1(i) ==
  /\ loc[i] = "broadcast1"
  /\ sent' = sent \cup
       {[type |-> "phase1", val |-> proposal[i], snd |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "waiting1"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

\* A message is received only if its type matches the receiver's current phase.
Receive(i, m) ==
  /\ loc[i] \in {"waiting1", "waiting2"}
  /\ m \in sent
  /\ m.type = IF loc[i] = "waiting1" THEN "phase1" ELSE "phase2"
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposal, estimate, decision, crashed, sent>>

\* After phase-1 messages from N-T distinct senders, compute the estimate.
Prepare(i) ==
  /\ loc[i] = "waiting1"
  /\ Cardinality({m.snd : m \in {x \in received[i] : x.type = "phase1"}}) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = Max2Of({view[i][j] : j \in 1..N})]
  /\ loc' = [loc EXCEPT ![i] = "broadcast2"]
  /\ UNCHANGED <<view, proposal, decision, crashed, sent, received>>

\* Broadcast a phase-2 message carrying both proposal and estimate.
Broadcast2(i) ==
  /\ loc[i] = "broadcast2"
  /\ sent' = sent \cup
       {[type |-> "phase2", val |-> proposal[i],
         snd |-> i, est |-> estimate[i]]}
  /\ loc' = [loc EXCEPT ![i] = "waiting2"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

\* A majority (N-T) of the same estimate arrives: decide and finish.
Decide(i) ==
  /\ loc[i] = "waiting2"
  /\ \E v \in Values :
       /\ Cardinality({m \in {x \in received[i] : x.type = "phase2"} :
                       m.est = v}) >= N - T
       /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

\* No estimate reached the majority, so choose a non-bottom value from the view.
Choose(i) ==
  /\ loc[i] = "waiting2"
  /\ \A v \in Values : Cardinality({m \in {x \in received[i] : x.type = "phase2"} :
                       m.est = v}) < N - T
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, sent, received>>

Picked(i) ==
  /\ loc[i] = "choosing"
  /\ Cardinality({j \in 1..N : view[i][j] # Bottom}) > 0
  /\ decision' = [decision EXCEPT ![i] = CHOOSE v \in Values :
                      Cardinality({j \in 1..N : view[i][j] = v}) > 0]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, sent, received>>

\* A crash is always available to a not-yet-crashed process while room remains.
Crash(i) ==
  /\ loc[i] # "crashed"
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposal, estimate, decision, sent, received>>

Next ==
  \/ \E i \in 1..N : Broadcast1(i) \/ Prepare(i) \/ Broadcast2(i)
                     \/ Decide(i) \/ Choose(i) \/ Picked(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in Msg : Receive(i, m)

\* Two independent fairness guarantees: each process progresses through its
\* two phases, and each process that reaches the choosing state eventually
\* picks a value, even when the receiver or broadcaster of messages is slow.
Fairness ==
  /\ \A i \in 1..N :
       /\ WF_vars(\E m \in Msg : Receive(i, m))
       /\ WF_vars(Prepare(i))
       /\ WF_vars(Decide(i) \/ Choose(i))
       /\ WF_vars(Picked(i))
  /\ WF_vars(\E i \in 1..N : Broadcast1(i))
  /\ WF_vars(\E i \in 1..N : Broadcast2(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Every decision is traceable to a proposing process, and no two processes
\* decide differently.
Validity == \A i \in 1..N : decision[i] # Bottom => decision[i] \in {proposal[j] : j \in 1..N}
Agreement == \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})
C1 == \A i \in 1..N : ((\E j \in 1..N : proposal[j] = Max2Of(Values)) /\ i >= F + 1) ~> loc[i] \in {"done", "crashed"}

Properties == Termination /\ C1

\* The reference configuration also checks each identifier's type at compile.
\* The constants have no intrinsic bound here; the model bounds are supplied
\* externally when the spec is instantiated for a concrete run.
====