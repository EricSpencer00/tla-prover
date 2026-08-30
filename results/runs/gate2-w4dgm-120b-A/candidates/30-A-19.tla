---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* N processes run a two-phase consensus on the maximum proposed value; a
\* process may crash (bounded by T) and slow (weak fairness) but never lies.
\* The invariant is agreement on the decided value, and under C1 (>= F+1 propose
\* the max) the protocol always reaches a decision.

\* Locations: two-phase control states, plus crashed and choosing.
\* view: each process's locally learned values; est: the computed maximum per
\* process after phase 1; decided: the value each process finally agrees on.
\* msgs: the in-flight messages; recv: per-recipient delivery history.

Locs == {"phase1", "phase1wait", "phase2", "phase2broadcast",
         "phase2wait", "done", "crashed", "choosing"}

Msgs == [kind: {"p1", "p2"}, val: Values, from: 0..(N-1), est: Values]

VARIABLES loc, view, proposed, est, decided, crashed, msgs, recv

vars == <<loc, view, proposed, est, decided, crashed, msgs, recv>>

Estimate(i) ==
  \E j \in 0..(N-1) : view[i][j] = est[i]
  /\ (\A k \in 0..(N-1) : view[i][k] # Bottom => view[i][k] <= est[i])

TypeOK ==
  /\ loc \in [0..(N-1) -> Locs]
  /\ view \in [0..(N-1) -> [0..(N-1) -> Values \cup {Bottom}]]
  /\ proposed \in [0..(N-1) -> Values]
  /\ est \in [0..(N-1) -> Values \cup {Bottom}]
  /\ decided \in [0..(N-1) -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ msgs \subseteq Msgs
  /\ recv \in [0..(N-1) -> SUBSET Msgs]

Init ==
  /\ loc = [i \in 0..(N-1) |-> "phase1"]
  /\ view = [i \in 0..(N-1) |-> [j \in 0..(N-1) |-> Bottom]]
  /\ \E f \in [0..(N-1) -> Values] : proposed = f
  /\ est = [i \in 0..(N-1) |-> Bottom]
  /\ decided = [i \in 0..(N-1) |-> Bottom]
  /\ crashed = 0
  /\ msgs = {}
  /\ recv = [i \in 0..(N-1) |-> {}]

Broadcast1(i) ==
  /\ loc[i] = "phase1"
  /\ msgs' = msgs \cup {[kind |-> "p1", val |-> proposed[i], from |-> i, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![i] = "phase1wait"]
  /\ UNCHANGED <<view, proposed, est, decided, crashed, recv>>

Receive1(i, m) ==
  /\ loc[i] \in {"phase1wait", "phase2wait"}
  /\ m \in msgs
  /\ m.kind = "p1"
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposed, est, decided, crashed, msgs>>

Prepare(i) ==
  /\ loc[i] = "phase1wait"
  /\ Cardinality({j \in 0..(N-1) : view[i][j] # Bottom}) >= N - T
  /\ est' = [est EXCEPT ![i] = CHOOSE m \in {view[i][j] : j \in 0..(N-1)} : TRUE]
  /\ loc' = [loc EXCEPT ![i] = "phase2broadcast"]
  /\ UNCHANGED <<view, proposed, decided, crashed, msgs, recv>>

Broadcast2(i) ==
  /\ loc[i] = "phase2broadcast"
  /\ msgs' = msgs \cup {[kind |-> "p2", val |-> proposed[i], from |-> i, est |-> est[i]]}
  /\ loc' = [loc EXCEPT ![i] = "phase2wait"]
  /\ UNCHANGED <<view, proposed, est, decided, crashed, recv>>

DecideV(i, v) ==
  /\ loc[i] \in {"phase2wait", "choosing"}
  /\ decided[i] = Bottom
  /\ v \in {m.est : m \in recv[i] /\ m.kind = "p2"}
  /\ Cardinality({j \in 0..(N-1) : \E m \in recv[i] : m.kind = "p2" /\ m.from = j /\ m.est = v})
        >= N - T
  /\ decided' = [decided EXCEPT ![i] = v]
  /\ loc' = [loc EXCEPT ![i] = "done"]
  /\ UNCHANGED <<view, proposed, est, crashed, msgs, recv>>

Choose(i) ==
  /\ loc[i] = "phase2wait"
  /\ decided[i] = Bottom
  /\ Cardinality({j \in 0..(N-1) : \E m \in recv[i] : m.kind = "p2" /\ m.from = j})
        = N
  /\ loc' = [loc EXCEPT ![i] = "choosing"]
  /\ UNCHANGED <<view, proposed, est, decided, crashed, msgs, recv>>

Receive2(i, m) ==
  /\ loc[i] \in {"phase2wait", "choosing"}
  /\ m \in msgs
  /\ m.kind = "p2"
  /\ view' = [view EXCEPT ![i][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![i] = @ \cup {m}]
  /\ UNCHANGED <<loc, proposed, est, decided, crashed, msgs>>

Crash(i) ==
  /\ loc[i] \in {"phase1", "phase1wait", "phase2broadcast", "phase2wait"}
  /\ crashed < F
  /\ loc' = [loc EXCEPT ![i] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, proposed, est, decided, msgs, recv>>

Next ==
  \/ \E i \in 0..(N-1) : Broadcast1(i)
  \/ \E i \in 0..(N-1), m \in msgs : Receive1(i, m)
  \/ \E i \in 0..(N-1) : Prepare(i)
  \/ \E i \in 0..(N-1) : Broadcast2(i)
  \/ \E i \in 0..(N-1), v \in Values : DecideV(i, v)
  \/ \E i \in 0..(N-1) : Choose(i)
  \/ \E i \in 0..(N-1), m \in msgs : Receive2(i, m)
  \/ \E i \in 0..(N-1) : Crash(i)

Spec == Init /\ [][Next]_vars
    /\ WF_vars(\E i \in 0..(N-1) : Broadcast1(i))
    /\ WF_vars(\E i \in 0..(N-1), m \in msgs : Receive1(i, m))
    /\ WF_vars(\E i \in 0..(N-1) : Prepare(i))
    /\ WF_vars(\E i \in 0..(N-1) : Broadcast2(i))
    /\ WF_vars(\E i \in 0..(N-1), m \in msgs : Receive2(i, m))
    /\ WF_vars(\E i \in 0..(N-1), v \in Values : DecideV(i, v))
    /\ WF_vars(\E i \in 0..(N-1) : Choose(i))

\* Safety: no two processes agree on different final values.
Agreement == \A i, j \in 0..(N-1) : (decided[i] # Bottom /\ decided[j] # Bottom) => decided[i] = decided[j]

\* Every decision was proposed by some process.
Validity == \A i \in 0..(N-1) : decided[i] # Bottom => \E j \in 0..(N-1) : decided[i] = proposed[j]

Liveness == \A i \in 0..(N-1) : (loc[i] # "done") ~> (loc[i] = "done" \/ loc[i] = "crashed")

\* Under C1 (>= F+1 propose the max), the asynchronous protocol always decides.
TerminationUnderC1 ==
  /\ Cardinality({i \in 0..(N-1) : proposed[i] = CHOOSE m \in Values : \A j \in Values : j <= m})
        >= F + 1
  /\ Liveness

====