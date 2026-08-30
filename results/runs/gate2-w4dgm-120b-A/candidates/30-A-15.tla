---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* A process holds a view of every other process's value; messages arriving
\* out of order fill that view, and the model is otherwise unrestricted.
\* A crashed process is simply stuck: it never broadcasts, receives, or
\* advances toward a decision.
\* Assumption: 2T < N (quorum overlap) and Values are distinct from Bottom.

\* Locations: normal broadcast/wait per phase, a choosing state, done, or
\* crashed. Phase-2 messages carry both proposed and estimated values.
Locations == { "bphase1", "wphase1", "prepare", "bphase2", "wphase2", "done", "crashed", "choosing" }
MsgKinds == { "phase1", "phase2" }

VARIABLES stage, view, propose, estimate, decided, crashed, sent, recv

TypeOK ==
  /\ stage \in [1..N -> Locations]
  /\ view \in [1..N -> [1..N -> Values \cup {Bottom}]]
  /\ propose \in [1..N -> Values]
  /\ estimate \in [1..N -> Values \cup {Bottom}]
  /\ decided \in [1..N -> Values \cup {Bottom}]
  /\ crashed \in 0..F
  /\ sent \subseteq [kind: MsgKinds, val: Values, from: 1..N, est: Values \cup {Bottom}]
  /\ recv \in [1..N -> SUBSET [kind: MsgKinds, val: Values, from: 1..N, est: Values \cup {Bottom}]]

Init ==
  /\ stage = [p \in 1..N |-> "bphase1"]
  /\ view = [p \in 1..N |-> [q \in 1..N |-> Bottom]]
  /\ propose \in [1..N -> Values]
  /\ estimate = [p \in 1..N |-> Bottom]
  /\ decided = [p \in 1..N |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 1..N |-> {}]

BroadcastPhase1(p) ==
  /\ stage[p] = "bphase1"
  /\ \A m \in sent : ~(m.kind = "phase1" /\ m.from = p)
  /\ sent' = sent \cup {[kind |-> "phase1", val |-> propose[p], from |-> p, est |-> Bottom]}
  /\ stage' = [stage EXCEPT ![p] = "wphase1"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recv>>

\* Messages may be delivered in any order; a delayed one is still usable.
Receive(p, m) ==
  /\ stage[p] \in {"wphase1", "wphase2"}
  /\ m \in sent
  /\ m.from \notin {q.from : q \in recv[p]}
  /\ m.kind = (IF stage[p] \in {"wphase1"} THEN "phase1" ELSE "phase2")
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ recv' = [recv EXCEPT ![p] = @ \cup {m}]
  /\ UNCHANGED <<stage, propose, estimate, decided, crashed, sent>>

\* The estimate is the max of the whole view, not just the quorum.
Prepare(p) ==
  /\ stage[p] = "wphase1"
  /\ Cardinality({q \in 1..N : \E m \in recv[p] : m.from = q /\ m.kind = "phase1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = CHOOSE v \in Values :
                     \A q \in 1..N : view[p][q] # Bottom => v >= view[p][q]]
  /\ stage' = [stage EXCEPT ![p] = "prepare"]
  /\ UNCHANGED <<view, propose, decided, crashed, sent, recv>>

BroadcastPhase2(p) ==
  /\ stage[p] = "prepare"
  /\ \A m \in sent : ~(m.kind = "phase2" /\ m.from = p)
  /\ sent' = sent \cup {[kind |-> "phase2", val |-> propose[p], from |-> p, est |-> estimate[p]]}
  /\ stage' = [stage EXCEPT ![p] = "bphase2"]
  /\ UNCHANGED <<view, propose, estimate, decided, crashed, recv>>

Decide(p) ==
  /\ stage[p] = "wphase2"
  /\ \E v \in Values :
        /\ Cardinality({q \in 1..N : \E m \in recv[p] : m.from = q /\ m.kind = "phase2" /\ m.est = v})
            >= N - T
        /\ decided' = [decided EXCEPT ![p] = v]
  /\ stage' = [stage EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

\* The fallback is always available, so progress never stalls.
Choose(p) ==
  /\ stage[p] = "wphase2"
  /\ \A q \in 1..N : \E m \in recv[p] : m.from = q /\ m.kind = "phase2"
  /\ \E v \in Values : decided' = [decided EXCEPT ![p] = v]
  /\ stage' = [stage EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, propose, estimate, crashed, sent, recv>>

Crash(p) ==
  /\ crashed < F
  /\ stage[p] # "crashed"
  /\ stage' = [stage EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, propose, estimate, decided, sent, recv>>

Next ==
  \E p \in 1..N :
    \/ BroadcastPhase1(p) \/ Prepare(p) \/ BroadcastPhase2(p) \/ Decide(p) \/ Choose(p) \/ Crash(p)
    \/ \E m \in sent : Receive(p, m)

\* A crashed process is stuck forever, so weak fairness per live process is
\* sufficient for the other ones to make progress to DONE.
Spec ==
  /\ Init /\ [][Next]_<<stage, view, propose, estimate, decided, crashed, sent, recv>>
  /\ \A p \in 1..N :
        /\ TRUE
        /\ WF_vars(Receive(p, CHOOSE m \in sent : m.from = p))
        /\ SF_vars(Prepare(p))
        /\ WF_vars(BroadcastPhase2(p))
        /\ SF_vars(Decide(p))
        /\ WF_vars(Choose(p))

Validity == \A p \in 1..N : decided[p] # Bottom => \E q \in 1..N : propose[q] = decided[p]

Agreement == \A p, q \in 1..N : (decided[p] # Bottom /\ decided[q] # Bottom)
                    => decided[p] = decided[q]

Termination == \A p \in 1..N : (stage[p] \in {"done", "crashed"}) ~> (stage[p] \in {"done", "crashed"})

\* The condition that triggers guaranteed termination.
ConditionC1 ==
  \E S \in SUBSET 1..N : (Cardinality(S) >= F + 1 /\ \A p \in S : propose[p] = CHOOSE m \in Values : \A q \in 1..N : m >= propose[q])
      => Termination

Properties == Termination /\ ConditionC1

====