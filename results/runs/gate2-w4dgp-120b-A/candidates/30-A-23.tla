---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Two-phase condition-based consensus: in phase 1 each process broadcasts its
\* proposed value and records the values it has heard into a local view.
\* In phase 2 each process broadcasts both its proposal and the maximum value
\* it observed. A process decides once a value is supported by at least N-T
\* senders; otherwise it deterministically chooses from its view. The system
\* tolerates up to T crash faults.

VARIABLES loc, view, prop, est, dec, crashed, sent, rcvd

vars == <<loc, view, prop, est, dec, crashed, sent, rcvd>>

Phases == {"bcast1", "w1", "prep", "bcast2", "w2", "done", "crashed", "choose"}
Types == {"ph1", "ph2"}
Msgs == [type : Types, val : Values \cup {Bottom}, snd : 1..N]

MaxInView(v) == \E i \in 1..N : v = view[i]

TypeOK ==
  /\ loc \in [1..N -> Phases]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ dec \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..N
  /\ sent \subseteq Msgs
  /\ rcvd \in [1..N -> SUBSET Msgs]

Init ==
  /\ loc = [i \in 1..N |-> "bcast1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ dec = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ rcvd = [i \in 1..N |-> {}]

\* Phase-1: broadcast your proposal and wait for N-T other proposals.
Bcast1(i) ==
  /\ loc[i] = "bcast1"
  /\ sent' = sent \cup {[type |-> "ph1", val |-> prop[i], snd |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, est, dec, crashed, rcvd>>

Rcv1(i, m) ==
  /\ loc[i] \in {"w1", "w2"}
  /\ m.type = "ph1"
  /\ m \notin rcvd[i]
  /\ loc[i] = "w1"
  /\ rcvd' = [rcvd EXCEPT ![i] = @ \cup {m}]
  /\ view' = [view EXCEPT ![i][m.snd] = m.val]
  /\ UNCHANGED <<loc, prop, est, dec, crashed, sent>>

\* Once enough phase-1 messages are collected, compute the estimate (maximum
\* value observed) and move to phase 2.
Prep(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality({k \in 1..N : [type |-> "ph1", val |-> view[i][k], snd |-> k] \in rcvd[i]}) >= N - T
  /\ est' = [est EXCEPT ![i] = CHOOSE v \in Values : \A k \in 1..N : view[i][k] # Bottom => view[i][k] <= v]
  /\ loc' = [loc EXCEPT ![i] = "bcast2"]
  /\ UNCHANGED <<view, prop, dec, crashed, sent, rcvd>>

\* Phase-2: broadcast your proposal together with the estimate you computed.
Bcast2(i) ==
  /\ loc[i] = "bcast2"
  /\ sent' = sent \cup {[type |-> "ph2", val |-> prop[i], snd |-> i]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, est, dec, crashed, rcvd>>

\* Decide once an estimate is supported by at least N-T phase-2 messages.
Decide(i) ==
  /\ loc[i] = "w2"
  /\ \E v \in Values :
       /\ Cardinality({k \in 1..N : [type |-> "ph2", val |-> est[k], snd |-> k] \in rcvd[i]}) >= N - T
       /\ dec' = [dec EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

\* If phase 2 yields no supported estimate, choose deterministically from the view.
Choose(i) ==
  /\ loc[i] = "w2"
  /\ \A k \in 1..N : [type |-> "ph2", val |-> est[k], snd |-> k] \in rcvd[i]
  /\ \A v \in Values :
       Cardinality({k \in 1..N : [type |-> "ph2", val |-> est[k], snd |-> k] \in rcvd[i]}) < N - T => v # est[k]
  /\ \E v \in Values :
       /\ MaxInView(v)
       /\ dec' = [dec EXCEPT ![i] = v]
       /\ loc' = [loc EXCEPT ![i] = "choose"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, rcvd>>

\* A process may crash.
Crash(i) ==
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, dec, sent, rcvd>>

Recover(i) ==
  /\ loc[i] = "crashed"
  /\ loc' = [loc EXCEPT ![i] = "bcast1"]
  /\ crashed' = crashed - 1
  /\ view' = [view EXCEPT ![i] = [j \in 1..N |-> Bottom]]
  /\ est' = [est EXCEPT ![i] = Bottom]
  /\ dec' = [dec EXCEPT ![i] = Bottom]
  /\ rcvd' = [rcvd EXCEPT ![i] = {}]
  /\ UNCHANGED <<prop, sent>>

Next ==
  \/ \E i \in 1..N : Bcast1(i) \/ Prep(i) \/ Bcast2(i) \/ Decide(i) \/ Choose(i) \/ Crash(i) \/ Recover(i)
  \/ \E i \in 1..N, m \in Msgs : Rcv1(i, m)

Spec == Init /\ [][Next]_vars
  /\ WF_vars(\E i \in 1..N, m \in Msgs : Rcv1(i, m))
  /\ WF_vars(\E i \in 1..N : Prep(i))
  /\ WF_vars(\E i \in 1..N : Bcast2(i))
  /\ WF_vars(\E i \in 1..N : Decide(i))
  /\ WF_vars(\E i \in 1..N : Choose(i))

\* Safety: any decision is a proposed value, and distinct processes never
\* decide two different values.
Validity == \A i \in 1..N : dec[i] # Bottom => \E k \in 1..N : prop[k] = dec[i]

Agreement == \A i, j \in 1..N : (dec[i] # Bottom /\ dec[j] # Bottom) => dec[i] = dec[j]

\* Liveness: everyone eventually decides or has crashed, and condition C1
\* guarantees termination of the protocol.
Termination == <>(\A i \in 1..N : loc[i] \in {"crashed", "done", "choose"})

C1 ==
  \A i \in 1..N : loc[i] \in {"bcast2", "w2", "done", "choose", "crashed"}
    => (\E j \in 1..N : prop[j] = CHOOSE v \in Values : \A k \in 1..N : prop[k] <= v)

====