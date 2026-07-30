---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* Every process may broadcast at most one message per phase; each message is
\* uniquely identified by the sender and phase it belongs to.
Message == [type : {"p1", "p2"}, prop : Values, from : 1..N, est : Values \cup {Bottom}]

VARIABLES loc, view, prop, est, decision, crashed, sent, received

vars == <<loc, view, prop, est, decision, crashed, sent, received>>

Bump(n) == IF n = N THEN 1 ELSE n + 1
MaxInView(v) == CHOOSE x \in Values : \A y \in Values : y \in {v[i] : i \in 1..N} => y <= x

TypeOK ==
  /\ loc \in [1..N -> {"b1", "w1", "prep", "b2", "w2", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ prop \in [1..N -> Values]
  /\ est \in [1..N -> Values \cup {Bottom}]
  /\ decision \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq Message
  /\ received \subseteq [1..N -> SUBSET Message]

Init ==
  /\ loc = [i \in 1..N |-> "b1"]
  /\ view = [i \in 1..N |-> [j \in 1..N |-> Bottom]]
  /\ prop \in [1..N -> Values]
  /\ est = [i \in 1..N |-> Bottom]
  /\ decision = [i \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ received = [i \in 1..N |-> {}]

\* Phase 1: broadcast the proposal.
BroadcastP1(i) ==
  /\ loc[i] = "b1"
  /\ sent' = sent \cup {[type |-> "p1", prop |-> prop[i], from |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "w1"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, received>>

\* Phase 1: receive a proposal into the local view.
RecvP1(i, m) ==
  /\ loc[i] = "w1"
  /\ m.type = "p1"
  /\ m.from \notin {mm.from : mm \in received[i]}
  /\ view' = [view EXCEPT ![i][m.from] = m.prop]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* Phase 1: enough distinct proposals received => compute estimate and move on.
GoPrep(i) ==
  /\ loc[i] = "w1"
  /\ Cardinality({mm.from : mm \in received[i]}) >= N - T
  /\ est' = [est EXCEPT ![i] = MaxInView(view[i])]
  /\ loc' = [loc EXCEPT ![i] = "prep"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, received>>

\* Phase 2: broadcast the proposal together with the computed estimate.
BroadcastP2(i) ==
  /\ loc[i] = "prep"
  /\ sent' = sent \cup {[type |-> "p2", prop |-> prop[i], from |-> i, est |-> est[i]]}
  /\ loc' = [loc EXCEPT ![i] = "w2"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, received>>

\* Phase 2: receive an estimate-stamped message into the local view.
RecvP2(i, m) ==
  /\ loc[i] = "w2"
  /\ m.type = "p2"
  /\ m.from \notin {mm.from : mm \in received[i]}
  /\ view' = [view EXCEPT ![i][m.from] = m.est]
  /\ received' = [received EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, prop, est, decision, crashed, sent>>

\* Phase 2: enough matching estimates received => adopt the decision and finish.
Decide(i, v) ==
  /\ loc[i] = "w2"
  /\ v # Bottom
  /\ Cardinality({mm.from : mm \in {m \in received[i] : m.type = "p2" /\ m.est = v}}) >= N - T
  /\ decision' = [decision EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, received>>

\* Phase 2: no estimate reached the threshold => go to the choosing state.
GoChoosing(i) ==
  /\ loc[i] = "w2"
  /\ {\infinity} \cup {mm.from : mm \in received[i]} = [1..N]
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, prop, est, decision, crashed, sent, received>>

\* Choosing: deterministically pick an available estimate from the local view.
PickAndDecide(i) ==
  /\ loc[i] = "choosing"
  /\ decision' = [decision EXCEPT ![i] = view[i][i]]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, prop, est, crashed, sent, received>>

\* Any process may crash while the fault budget is available.
Crash(i) ==
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, est, decision, sent, received>>

Next ==
  \/ \E i \in 1..N : BroadcastP1(i) \/ GoPrep(i) \/ BroadcastP2(i) \/ GoChoosing(i)
                       \/ PickAndDecide(i) \/ Crash(i)
  \/ \E i \in 1..N, m \in Message : RecvP1(i, m) \/ RecvP2(i, m)
  \/ \E i \in 1..N, v \in Values \cup {Bottom} : Decide(i, v)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in 1..N, m \in Message : RecvP1(i, m))
        /\ WF_vars(\E i \in 1..N, m \in Message : RecvP2(i, m))
        /\ WF_vars(\E i \in 1..N : GoPrep(i))
        /\ WF_vars(\E i \in 1..N : BroadcastP2(i))
        /\ WF_vars(\E i \in 1..N : GoChoosing(i))
        /\ WF_vars(\E i \in 1..N : PickAndDecide(i))

Validity == \A i \in 1..N : decision[i] # Bottom => decision[i] \in {prop[j] : j \in 1..N}

Agreement == \A i, j \in 1..N : (decision[i] # Bottom /\ decision[j] # Bottom) => decision[i] = decision[j]

Termination == <>(\A i \in 1..N : loc[i] \in {"done", "crashed"})

\* Conditional termination under condition C1: enough processes propose the
\* maximum value that the protocol is then guaranteed to agree on.
ConditionalTermination ==
  (Cardinality({i \in 1..N : prop[i] = MaxInView([j \in 1..N |-> prop[j]])}) >= F + 1) ~> Termination

\* The configuration requires the two standard bounds; the safety of the
\* protocol depends on them, so they are explicitly listed as invariants.
BoundAssumptions ==
  /\ 2 * T < N
  /\ F <= T
  /\ N > 0
  /\ Bottom \notin Values

TypeOKInvariant == TypeOK /\ BoundAssumptions

Properties == Termination /\ ConditionalTermination

====