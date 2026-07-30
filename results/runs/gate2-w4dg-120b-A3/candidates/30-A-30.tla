---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A message is either phase-1 or phase-2; phase-2 additionally carries the
\* estimated value the sender computed.  Messages carry the sender's id.
Message == [type : {"phase1", "phase2"}, val : Values, sid : 1 .. N, est : Values]

VARIABLES loc, v, estimated, decided, crashedCount, msgs, recv
vars == <<loc, v, estimated, decided, crashedCount, msgs, recv>>

Sends == {m \in msgs : m.sid = p}
Seen(p, t) == Cardinality({m \in Sends : m.type = t})
SeenVals(p, t, x) == Cardinality({m \in Sends : m.type = t /\ m.est = x})

MaxValOf(v0) == CHOOSE m \in Values : \A x \in Values : x # m => x <= m

TypeOK ==
  /\ loc \in [1 .. N -> {"phase1", "p1wait", "prepare", "phase2", "p2wait", "done", "crashed", "choose"}]
  /\ v \in [1 .. N -> Values]
  /\ estimated \in [1 .. N -> Values \cup {Bottom}]
  /\ decided \in [1 .. N -> Values \cup {Bottom}]
  /\ crashedCount \in 0 .. F
  /\ msgs \subseteq Message
  /\ recv \in [1 .. N -> SUBSET Message]

Init ==
  /\ loc = [p \in 1 .. N |-> "phase1"]
  /\ v \in [1 .. N -> Values]
  /\ estimated = [p \in 1 .. N |-> Bottom]
  /\ decided = [p \in 1 .. N |-> Bottom]
  /\ crashedCount = 0
  /\ msgs = {}
  /\ recv = [p \in 1 .. N |-> {}]

\* Phase 1: the first broadcast disseminates only the proposed value.
BroadcastPhase1(p) ==
  /\ loc[p] = "phase1"
  /\ msgs' = msgs \cup {[type |-> "phase1", val |-> v[p], sid |-> p, est |-> Bottom]}
  /\ loc' = [loc EXCEPT ![p] = "p1wait"]
  /\ UNCHANGED <<v, estimated, decided, crashedCount, recv>>

\* Receivers fill in their local view only when the message matches the phase.
Receive(p, m) ==
  /\ loc[p] \in {"p1wait", "p2wait"}
  /\ m \in msgs
  /\ m \notin recv[p]
  /\ loc[p] = CASE m.type = "phase1" -> "p1wait" [] m.type = "phase2" -> "p2wait"
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED <<loc, v, estimated, decided, crashedCount, msgs>>

\* The threshold is N - T, not N - F: the protocol tolerates up to T faults.
StartPhase2(p) ==
  /\ loc[p] = "p1wait"
  /\ Seen(p, "phase1") >= N - T
  /\ estimated' = [estimated EXCEPT ![p] = MaxValOf(v[p])]
  /\ loc' = [loc EXCEPT ![p] = "phase2"]
  /\ UNCHANGED <<v, decided, crashedCount, msgs, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "phase2"
  /\ msgs' = msgs \cup {[type |-> "phase2", val |-> v[p], sid |-> p, est |-> estimated[p]]}
  /\ loc' = [loc EXCEPT ![p] = "p2wait"]
  /\ UNCHANGED <<v, estimated, decided, crashedCount, recv>>

DecideOnThreshold(p, x) ==
  /\ loc[p] = "p2wait"
  /\ SeenVals(p, "phase2", x) >= N - T
  /\ decided' = [decided EXCEPT ![p] = x]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<v, estimated, crashedCount, msgs, recv>>

\* Deterministic tie-breaking: the process picks a visible value.
Choose(p, x) ==
  /\ loc[p] = "choose"
  /\ x \in {m.val : m \in recv[p]}
  /\ decided' = [decided EXCEPT ![p] = x]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<v, estimated, crashedCount, msgs, recv>>

DecideMissing(p) ==
  /\ loc[p] = "p2wait"
  /\ \A x \in Values : SeenVals(p, "phase2", x) < N - T
  /\ loc' = [loc EXCEPT ![p] = "choose"]
  /\ UNCHANGED <<v, estimated, decided, crashedCount, msgs, recv>>

Crash(p) ==
  /\ loc[p] \notin {"done", "crashed"}
  /\ crashedCount < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED <<v, estimated, decided, msgs, recv>>

Next ==
  \/ \E p \in 1 .. N : BroadcastPhase1(p)
  \/ \E p \in 1 .. N, m \in Message : Receive(p, m)
  \/ \E p \in 1 .. N : StartPhase2(p)
  \/ \E p \in 1 .. N : BroadcastPhase2(p)
  \/ \E p \in 1 .. N, x \in Values : DecideOnThreshold(p, x)
  \/ \E p \in 1 .. N, x \in Values : Choose(p, x)
  \/ \E p \in 1 .. N : DecideMissing(p)
  \/ \E p \in 1 .. N : Crash(p)

\* Weak fairness on the loop that feeds each phase, and on the deterministic
\* tie-breaking step, since the others are guarded.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in 1 .. N, m \in Message : Receive(p, m))
  /\ WF_vars(\E p \in 1 .. N : BroadcastPhase1(p))
  /\ WF_vars(\E p \in 1 .. N : BroadcastPhase2(p))
  /\ WF_vars(\E p \in 1 .. N : StartPhase2(p))
  /\ WF_vars(\E p \in 1 .. N, x \in Values : Choose(p, x))

Validity == \A p \in 1 .. N : decided[p] # Bottom => decided[p] \in Values
Agreement == \A p \in 1 .. N : decided[p] # Bottom => decided[p] = decided[N]

Terminate == <>(\A p \in 1 .. N : loc[p] \in {"done", "crashed"})
CondTerminate == (Cardinality({p \in 1 .. N : v[p] = MaxValOf(v[1])}) >= F + 1) ~> Terminate

====