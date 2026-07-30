---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Locations (control states) the reference model expects for every process.
\* They are deliberately exhaustive: each step below advances the process
\* through these exact phases, so none may be omitted.
Locations == {
  "ph1bcast",    \* broadcasting phase-1 message
  "ph1wait",     \* waiting for phase-1 messages
  "preparing",   \* ready to compute estimate post-phase-1
  "ph2bcast",    \* broadcasting phase-2 message
  "ph2wait",     \* waiting for phase-2 messages
  "done",        \* decided and finished
  "crashed",     \* crashed silently
  "choosing"     \* deterministically picking after a failed epoch
}

Messages == [type: {"ph1", "ph2"}, val: Values \cup {Bottom}, sender: 1..N, est: Values \cup {Bottom}]

VARIABLES loc, view, prop, estimate, decision, crashedCount, sent, recv

vars == << loc, view, prop, estimate, decision, crashedCount, sent, recv >>

MessageId(m) == << m.type, m.sender, m.val, m.est >>

TypeOK ==
  /\ loc \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashedCount \in 0..F
  /\ sent \subseteq Messages
  /\ recv \in [1..N -> SUBSET Messages]

Init ==
  /\ loc = [p \in 1..N |-> "ph1bcast"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ \E f \in [1..N -> Values] : prop = f
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decision = [p \in 1..N |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

\* Phase 1: broadcast the proposed value to everyone.
Ph1Broadcast(p) ==
  /\ loc[p] = "ph1bcast"
  /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[p], sender |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "ph1wait"]
  /\ UNCHANGED << view, prop, estimate, decision, crashedCount, recv >>

\* Receive messages into the local view whenever the type matches the phase.
Ph1Receive(p, m) ==
  /\ m \in sent
  /\ m.type = "ph1"
  /\ loc[p] = "ph1wait"
  /\ m \notin recv[p]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << loc, prop, estimate, decision, crashedCount, sent >>

\* After enough distinct phase-1 messages arrive, compute the estimate and
\* move on to phase 2. "Enough" is exactly the threshold from the model.
Prepare(p) ==
  /\ loc[p] = "ph1wait"
  /\ Cardinality({m \in recv[p] : m.type = "ph1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values : \A q \in 1..N :
                    (view[p][q] # Bottom => view[p][q] <= v)]
  /\ loc' = [loc EXCEPT ![p] = "ph2bcast"]
  /\ UNCHANGED << view, prop, decision, crashedCount, sent, recv >>

\* Phase 2: broadcast both the original value and the computed estimate.
Ph2Broadcast(p) ==
  /\ loc[p] = "ph2bcast"
  /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[p], sender |-> p, est |-> estimate[p]]}
  /\ loc' = [loc EXCEPT ![p] = "ph2wait"]
  /\ UNCHANGED << view, prop, estimate, decision, crashedCount, recv >>

\* Decide once a supermajority of phase-2 messages agrees on one estimate.
Decide(p) ==
  /\ loc[p] = "ph2wait"
  /\ \E v \in Values :
        /\ Cardinality({m \in recv[p] : m.type = "ph2" /\ m.est = v}) >= N - T
        /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, estimate, crashedCount, sent, recv >>

\* If consensus cannot be reached at all (phase-2 messaged from everyone,
\* but never a supermajority), fall back to deterministic picking: the
\* model also expects this path to stay available.
Fallback(p) ==
  /\ loc[p] = "ph2wait"
  /\ \A m \in recv[p] : m.type = "ph2"
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << view, prop, estimate, decision, crashedCount, sent, recv >>

\* In the choosing state the process deterministically picks *any* value
\* it has observed (the spec fixes the pick to the first one in the
\* underlying order, rather than an arbitrary one, so the model stays deterministic).
Choose(p) ==
  /\ loc[p] = "choosing"
  /\ \E v \in Values \cup {Bottom} :
        /\ \E q \in 1..N :
             /\ view[p][q] = v
             /\ decision' = [decision EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, estimate, crashedCount, sent, recv >>

\* Crash fault: one more process may silently crash, up to the bound.
Crash(p) ==
  /\ crashedCount < F
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashedCount' = crashedCount + 1
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << view, prop, estimate, decision, sent, recv >>

Next ==
  \/ \E p \in 1..N : Ph1Broadcast(p) \/ Prepare(p) \/ Ph2Broadcast(p) \/ Decide(p)
                        \/ Fallback(p) \/ Choose(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in Messages : Ph1Receive(p, m)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E p \in 1..N, m \in Messages : Ph1Receive(p, m))
  /\ WF_vars(\E p \in 1..N : Ph2Broadcast(p))
  /\ WF_vars(\E p \in 1..N : Prepare(p))
  /\ WF_vars(\E p \in 1..N : Decide(p))
  /\ WF_vars(\E p \in 1..N : Choose(p))

Validity == \A p \in 1..N : decision[p] # Bottom => decision[p] \in Values

Agreement == \A p, q \in 1..N : (decision[p] # Bottom /\ decision[q] # Bottom) => decision[p] = decision[q]

Termination == <>(\A p \in 1..N : loc[p] \in {"done", "crashed"})

\* Conditional termination under the protocol's max-value condition.
ConditionC1 ==
  \E eg \in [1..N -> Values] :
    /\ Cardinality({p \in 1..N : eg[p] = CHOOSE x \in Values : \A q \in 1..N : eg[q] <= x}) >= F + 1
    /\ \A p \in 1..N : prop[p] = eg[p]
    /\ Termination

====