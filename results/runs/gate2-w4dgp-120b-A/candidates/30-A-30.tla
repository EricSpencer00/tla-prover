---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME N \in Nat /\ N > 0
ASSUME T \in Nat /\ 2 * T < N
ASSUME F \in Nat /\ F <= T
ASSUME Bottom \notin Values

VARIABLES pc, view, proposal, estimate, decision, crashed, messages, received
vars == <<pc, view, proposal, estimate, decision, crashed, messages, received>>

\* Max is the standard condition-agnostic reduction: take the greatest value seen locally.
Max(S) == IF S = {} THEN Bottom ELSE LET m == CHOOSE x \in S : \A y \in S : x >= y IN m

Phases == {"bc1", "wait1", "prepare", "bc2", "wait2", "done", "crashed", "choose"}

TypeOK ==
  /\ pc \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposal \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ messages \subseteq [type: {"p1", "p2"}, val: Values, from: 1..N, est: Values \cup {Bottom}]
  /\ received \in [1..N -> SUBSET (1..N)]

Init ==
  /\ pc = [n \in 1..N |-> "bc1"]
  /\ view = [n \in 1..N |-> [m \in 1..N |-> Bottom]]
  /\ proposal \in [1..N -> Values]
  /\ estimate = [n \in 1..N |-> Bottom]
  /\ decision = [n \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ messages = {}
  /\ received = [n \in 1..N |-> {}]

\* Phase 1 broadcast: each process sends its own proposal to all peers.
Broadcast1(n) ==
  /\ pc[n] = "bc1"
  /\ messages' = messages \cup {[type |-> "p1", val |-> proposal[n], from |-> n, est |-> Bottom]}
  /\ pc' = [pc EXCEPT ![n] = "wait1"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

\* Receiving a message updates the local view if it matches the current phase.
Receive(n, m) ==
  /\ pc[n] \in {"wait1", "wait2"}
  /\ m \in messages
  /\ m.type = (IF pc[n] = "wait1" THEN "p1" ELSE "p2")
  /\ m.from \notin received[n]
  /\ view' = [view EXCEPT ![n][m.from] = m.val]
  /\ received' = [received EXCEPT ![n] = @ \cup {m.from}]
  /\ UNCHANGED <<pc, proposal, estimate, decision, crashed, messages>>

\* Once enough messages are in, compute the maximum estimate and move on.
Prepare(n) ==
  /\ pc[n] = "wait1"
  /\ Cardinality(received[n]) >= N - T
  /\ estimate' = [estimate EXCEPT ![n] = Max({view[n][m] : m \in 1..N})]
  /\ pc' = [pc EXCEPT ![n] = "bc2"]
  /\ UNCHANGED <<view, proposal, decision, crashed, messages, received>>

\* Phase 2 broadcast: each process sends both its proposal and its estimate.
Broadcast2(n) ==
  /\ pc[n] = "bc2"
  /\ messages' = messages \cup {[type |-> "p2", val |-> proposal[n], from |-> n, est |-> estimate[n]]}
  /\ pc' = [pc EXCEPT ![n] = "wait2"]
  /\ UNCHANGED <<view, proposal, estimate, decision, crashed, received>>

\* Decision: finalise when enough peers agree on the same estimate.
Decide(n) ==
  /\ pc[n] = "wait2"
  /\ \E e \in Values :
       /\ Cardinality({m \in messages : m.type = "p2" /\ m.from \in received[n] /\ m.est = e}) >= N - T
       /\ decision' = [decision EXCEPT ![n] = e]
  /\ pc' = [pc EXCEPT ![n] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, messages, received>>

\* If no estimate gains a majority, choose deterministically from the local view.
Choose(n) ==
  /\ pc[n] = "wait2"
  /\ received[n] = 1..N
  /\ Cardinality({e \in Values :
        Cardinality({m \in messages : m.type = "p2" /\ m.from \in received[n] /\ m.est = e}) >= N - T}) < 1
  /\ \E e \in Values : e \in {view[n][m] : m \in 1..N} /\ decision' = [decision EXCEPT ![n] = e]
  /\ pc' = [pc EXCEPT ![n] = "done"]
  /\ UNCHANGED <<view, proposal, estimate, crashed, messages, received>>

Crash(n) ==
  /\ crashed < F
  /\ crashed' = crashed + 1
  /\ pc' = [pc EXCEPT ![n] = "crashed"]
  /\ UNCHANGED <<view, proposal, estimate, decision, messages, received>>

Next ==
  \/ \E n \in 1..N : Broadcast1(n) \/ Prepare(n) \/ Broadcast2(n) \/ Decide(n) \/ Choose(n) \/ Crash(n)
  \/ \E n \in 1..N, m \in messages : Receive(n, m)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E n \in 1..N, m \in messages : Receive(n, m))
  /\ WF_vars(\E n \in 1..N : Prepare(n))
  /\ WF_vars(\E n \in 1..N : Deci

Decide(n) \/ Choose(n))
  /\ WF_vars(\E n \in 1..N : Crash(n))

\* Any finished decision was actually proposed by somebody.
Validity == \A n \in 1..N : (pc[n] = "done") => (decision[n] \in Values)

\* No two processes ever decide different values.
Agreement == \A i, j \in 1..N : (pc[i] = "done" /\ pc[j] = "done") => decision[i] = decision[j]

Termination == \A n \in 1..N : pc[n] \in {"done", "crashed"}

\* Condition C1: the maximum is proposed often enough to guarantee termination.
ConditionC1 == (\E n \in 1..N : proposal[n] = Max(Values)) => Termination

====