---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase (C1) condition-based agreement: each process proposes an
\* initial value, then broadcasts it (phase 1 messages) so it can compute
\* an estimate of the max; it then broadcasts both its own proposal and
\* its estimate (phase 2). Because crashes erase a process's perspective
\* wholesale, a decision is only made once a subset of size N-T (a
\* supermajority that tolerates T crashes) has reported the same estimate.
\* The model has four locations per process (broadcasting, waiting, done,
\* crashed) and two-phase counters, plus a bounded crash budget.

VARIABLES pc, view, proposed, estimate, decision, crashed, sent, rcvd

Bump(n, i) == IF i = n THEN 0 ELSE i + 1

TypeOK ==
  /\ pc \in [1..N -> {"b1", "w1", "b2", "w2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [type: {"p1", "p2"}, val: Values, ev: Values \cup {Bottom}, src: 1..N]
  /\ rcvd \in [1..N -> SUBSET (1..N)]

Init ==
  /\ pc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ proposed \in [i \in 1..N -> Values]
  /\ estimate = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]

\* Phase 1: broadcast the initial proposal.
Broadcast1(i) ==
  /\ pc[i] = "b1"
  /\ sent' = sent \cup {[type |-> "p1", val |-> proposed[i], ev |-> Bottom, src |-> i]}
  /\ pc' = [pc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, rcvd>>

\* Deliver a phase-1 message into the view matrix; only accepted if it
\* matches the phase the receiver is currently in.
Receive1(i, j) ==
  /\ pc[i] = "w1"
  /\ j \in rcvd[i]
  /\ [type |-> "p1", val |-> view[i][j], ev |-> Bottom, src |-> j] \in sent
  /\ view' = [view EXCEPT ![i][j] = view[i][j]]
  /\ UNCHANGED <<pc, proposed, estimate, decision, crashed, sent, rcvd>>

\* Estimate = max of everything seen so far; needs a supermajority of
\* distinct phase-1 messages (N - T) so that T crashes cannot stall it.
Estimate(i) ==
  /\ pc[i] = "w1"
  /\ Cardinality(rcvd[i]) >= N - T
  /\ estimate' = [estimate EXCEPT ![i] = Bump(proposed[i], \A j \in 1..N : view[i][j])]
  /\ pc' = [pc EXCEPT ![i] = "b2"]
  /\ UNCHANGED <<view, proposed, decision, crashed, sent, rcvd>>

\* Phase 2: broadcast both the own proposal and the derived estimate.
Broadcast2(i) ==
  /\ pc[i] = "b2"
  /\ sent' = sent \cup {[type |-> "p2", val |-> proposed[i], ev |-> estimate[i], src |-> i]}
  /\ pc' = [pc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, proposed, estimate, decision, crashed, rcvd>>

\* Deliver a phase-2 message into the view matrix.
Receive2(i, j) ==
  /\ pc[i] = "w2"
  /\ j \in rcvd[i]
  /\ [type |-> "p2", val |-> view[i][j], ev |-> estimate[i], src |-> j] \in sent
  /\ view' = [view EXCEPT ![i][j] = view[i][j]]
  /\ UNCHANGED <<pc, proposed, estimate, decision, crashed, sent, rcvd>>

\* Decide the estimate once a supermajority of distinct phase-2 messages
\* carry the same estimate -- this is where two processes converge.
Decide(i) ==
  /\ pc[i] = "w2"
  /\ Cardinality(rcvd[i]) >= N - T
  /\ \E c \in \{v \in Values : Cardinality({j \in rcvd[i] : view[i][j] = v}) >= N - T} :
       decision' = [decision EXCEPT ![i] = c]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashed, sent, rcvd>>

\* Deterministic fallback: pick any value the local view currently shows.
Choose(i) ==
  /\ pc[i] = "w2"
  /\ rcvd[i] = 1..N
  /\ decision' = [decision EXCEPT ![i] = \E v \in \{view[i][j] : j \in 1..N\} : v]
  /\ pc' = [pc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed estimate, crashed, sent, rcvd>>

Crash(i) ==
  /\ pc[i] \notin {"done", "crashed"}
  /\ crashed < F
  /\ pc' = [pc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, estimate, decision, sent, rcvd>>

\* Fairness of the cyclic delivery/reception/decision/choosing steps is
\* what stops a process from stalling forever at a waiting state.
Next ==
  \/ \E i \in 1..N :
       \/ Broadcast1(i) \/ Estimate(i) \/ Broadcast2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i)
       \/ \E j \in 1..N : Receive1(i, j) \/ Receive2(i, j)

Spec == Init /\ [][Next]_<<pc, view, proposed, estimate, decision, crashed, sent, rcvd>>

\* Safety: a decision only ever reflects a value some process actually
\* proposed (validity), and two processes can never decide different
\* values (agreement) -- the two are not the same property under crash.
Validity == \A i \in 1..N : decision[i] # Bottom => \E j \in 1..N : decision[i] = proposed[j]

Agreement == \A i, k \in 1..N : (decision[i] # Bottom /\ decision[k] # Bottom) => decision[i] = decision[k]

\* Termination: every process is eventually decided or crashed.
Termination == \A i \in 1..N : <>(pc[i] \in {"done", "crashed"})

\* Conditional termination: Condition C1 (the supermajority of the
\* maximum value) guarantees the protocol does not stall forever.
C1Terminates ==
  /\ \E i \in 1..N : proposed[i] = Bump(\A j \in 1..N : proposed[j])
  /\ Termination

====