---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

VARIABLES loc, view, proposed, estimate, decided, crashes, sent, recv

vars == <<loc, view, proposed, estimate, decided, crashes, sent, recv>>

\* Two independent runs of the same protocol share a value set; the
\* safety/termination hinges only on how many propose the *maximum*.
MaxV == CHOOSE v \in Values : \A w \in Values : w <= v
Proposers(v) == { p \in 1..N : proposed[p] = v }

TypeOK ==
  /\ loc \in [1..N -> {"phase1broad", "phase1wait", "prepare",
                       "phase2broad", "phase2wait", "done", "crashed", "choosing"}]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ proposed \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashes \in 0..F
  /\ sent \subseteq [type: {"phase1", "phase2"}, val: Values, sender: 1..N]
  /\ recv \in [1..N -> SUBSET (1..N)]

Init ==
  /\ loc = [p \in 1..N |-> "phase1broad"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ proposed \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashes = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ loc[p] = "phase1broad"
  /\ sent' = sent \cup {[type |-> "phase1", val |-> proposed[p], sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "phase1wait"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, recv>>

ReceivePhase1(p, m) ==
  /\ loc[p] \in {"phase1wait", "prepare"}
  /\ m.type = "phase1"
  /\ m.sender \in recv[p]
  /\ view[p][m.sender] = Bottom
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m.sender}]
  /\ UNCHANGED <<loc, proposed, estimate, decided, crashes, sent>>

\* Each process uses only its own view to compute, so the max is computed
\* locally and may well be below the true global max.
ComputeEstimate(p) ==
  /\ loc[p] = "phase1wait"
  /\ Cardinality(recv[p]) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                                        \A q \in 1..N : view[p][q] # Bottom => view[p][q] <= v]
  /\ loc' = [loc EXCEPT ![p] = "phase2broad"]
  /\ UNCHANGED <<view, proposed, decided, crashes, sent, recv>>

BroadcastPhase2(p) ==
  /\ loc[p] = "phase2broad"
  /\ sent' = sent \cup {[type |-> "phase2", val |-> proposed[p],
                         sender |-> p]}
  /\ loc' = [loc EXCEPT ![p] = "phase2wait"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, recv>>

\* A decision requires a strictly supermajority of distinct senders on
\* *one* estimated value, which is what stops two processes picking
\* different values from conflicting views.
DecideBySupermajority(p, e) ==
  /\ loc[p] = "phase2wait"
  /\ Cardinality({q \in 1..N :
        \E m \in sent : m.type = "phase2" /\ m.sender = q /\ estimate[p] = e}) >= N - T
  /\ decided' = [decided EXCEPT ![p] = e]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashes, sent, recv>>

ChooseFallback(p) ==
  /\ loc[p] = "phase2wait"
  /\ recv[p] = 1..N
  /\ \A e \in Values :
        Cardinality({q \in 1..N :
          \E m \in sent : m.type = "phase2" /\ m.sender = q /\ estimate[p] = e})
            < N - T
  /\ loc' = [loc EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, proposed, estimate, decided, crashes, sent, recv>>

FallbackDecide(p, v) ==
  /\ loc[p] = "choosing"
  /\ v \in { view[p][q] : q \in 1..N } \ {Bottom}
  /\ decided' = [decided EXCEPT ![p] = v]
  /\ loc' = [loc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, proposed, estimate, crashes, sent, recv>>

Crash(p) ==
  /\ loc[p] \notin {"crashed", "done"}
  /\ crashes < F
  /\ loc' = [loc EXCEPT ![p] = "crashed"]
  /\ crashes' = crashes + 1
  /\ UNCHANGED <<view, proposed, estimate, decided, sent, recv>>

Next ==
  \/ \E p \in 1..N: BroadcastPhase1(p) \/ ComputeEstimate(p)
                     \/ BroadcastPhase2(p) \/ ChooseFallback(p) \/ Crash(p)
  \/ \E p \in 1..N, m \in sent: ReceivePhase1(p, m)
  \/ \E p \in 1..N, e \in Values: DecideBySupermajority(p, e)
  \/ \E p \in 1..N, v \in Values: FallbackDecide(p, v)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 1..N: WF_vars(\E m \in sent: ReceivePhase1(p, m))
  /\ \A p \in 1..N: WF_vars(ComputeEstimate(p))
  /\ \A p \in 1..N: WF_vars(BroadcastPhase2(p))
  /\ \A p \in 1..N: WF_vars(\E e \in Values: DecideBySupermajority(p, e))
  /\ \A p \in 1..N: WF_vars(ChooseFallback(p))
  /\ \A p \in 1..N: WF_vars(\E v \in Values: FallbackDecide(p, v))

Validity == \A p \in 1..N: decided[p] # Bottom => \E q \in 1..N: proposed[q] = decided[p]
Agreement == \A p1, p2 \in 1..N: (decided[p1] # Bottom /\ decided[p2] # Bottom)
                            => decided[p1] = decided[p2]

Termination == \A p \in 1..N: <>(loc[p] \in {"done", "crashed"})

\* Conditional termination under Condition C1 (the majority-of-faults case).
TerminateUnderC1 == Proposers(MaxV) \supseteq 1..(F + 1) ~> (\A p \in 1..N: loc[p] \in {"done", "crashed"})

====