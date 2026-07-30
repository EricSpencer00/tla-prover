---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F, Values, Bottom

ASSUME /\ N \in Nat /\ N > 0
       /\ T \in Nat /\ 2 * T < N
       /\ F \in Nat /\ F <= T
       /\ Bottom \notin Values
       /\ Values # {}

VARIABLES phase, view, prop, estimate, decision, crashed, sent, recv

vars == <<phase, view, prop, estimate, decision, crashed, sent, recv>>

Message == [type: {"p1", "p2"}, val: Values, from: 0 .. N - 1, est: Values \cup {Bottom}]

Phases == {"bc1", "w1", "prep", "bc2", "w2", "done", "crashed", "choosing"}

TypeOK ==
  /\ phase \in [0 .. N - 1 -> Phases]
  /\ view \in [0 .. N - 1 -> [0 .. N - 1 -> Values \cup {Bottom}]]
  /\ prop \in [0 .. N - 1 -> Values]
  /\ estimate \in [0 .. N - 1 -> Values \cup {Bottom}]
  /\ decision \in [0 .. N - 1 -> Values \cup {Bottom}]
  /\ crashed \in 0 .. N
  /\ sent \subseteq Message
  /\ recv \in [0 .. N - 1 -> SUBSET Message]

Init ==
  /\ phase = [p \in 0 .. N - 1 |-> "bc1"]
  /\ view = [p \in 0 .. N - 1 |-> [q \in 0 .. N - 1 |-> Bottom]]
  /\ \E f \in [0 .. N - 1 -> Values] : prop = f
  /\ estimate = [p \in 0 .. N - 1 |-> Bottom]
  /\ decision = [p \in 0 .. N - 1 |-> Bottom]
  /\ crashed = 0
  /\ sent = {}
  /\ recv = [p \in 0 .. N - 1 |-> {}]

BroadcastP1(p) ==
  /\ phase[p] = "bc1"
  /\ sent' = sent \union {[type |-> "p1", val |-> prop[p], from |-> p, est |-> Bottom]}
  /\ phase' = [phase EXCEPT ![p] = "w1"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

\* A message is only incorporated into the local view if it matches the
\* phase the receiver currently believes it is in.
RecvP1(p, m) ==
  /\ phase[p] \in {"w1", "prep"}
  /\ m.type = "p1"
  /\ view[p][m.from] = Bottom
  /\ view' = [view EXCEPT ![p][m.from] = m.val]
  /\ UNCHANGED <<phase, prop, estimate, decision, crashed, sent, recv>>

\* Phase 1 only advances once a quorum of distinct senders has been heard.
Prepare(p) ==
  /\ phase[p] = "w1"
  /\ Cardinality({m \in recv[p] : m.type = "p1"}) >= N - T
  /\ estimate' = [estimate EXCEPT ![p] = Max({view[p][q] : q \in 0 .. N - 1} \ {Bottom})]
  /\ phase' = [phase EXCEPT ![p] = "bc2"]
  /\ UNCHANGED <<view, prop, decision, crashed, sent, recv>>

BroadcastP2(p) ==
  /\ phase[p] = "bc2"
  /\ sent' = sent \union {[type |-> "p2", val |-> prop[p], from |-> p, est |-> estimate[p]]}
  /\ phase' = [phase EXCEPT ![p] = "w2"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, recv>>

RecvP2(p, m) ==
  /\ phase[p] \in {"w2", "done", "choosing"}
  /\ m.type = "p2"
  /\ recv' = [recv EXCEPT ![p] = @ \union {m}]
  /\ UNCHANGED <<phase, view, prop, estimate, decision, crashed, sent>>

Decide(p) ==
  /\ phase[p] = "w2"
  /\ \E e \in Values :
       /\ Cardinality({m \in recv[p] : m.type = "p2" /\ m.est = e}) >= N - T
       /\ decision' = [decision EXCEPT ![p] = e]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Choose(p) ==
  /\ phase[p] = "w2"
  /\ \A e \in Values :
       Cardinality({m \in recv[p] : m.type = "p2" /\ m.est = e}) < N - T
  /\ phase' = [phase EXCEPT ![p] = "choosing"]
  /\ UNCHANGED <<view, prop, estimate, decision, crashed, sent, recv>>

\* Deterministic choice: always pick the smallest value still present in the view.
PickChoice(p) ==
  /\ phase[p] = "choosing"
  /\ decision' = [decision EXCEPT ![p] = CHOOSE x \in {view[p][q] : q \in 0 .. N - 1} :
                     \/ \A y \in {view[p][r] : r \in 0 .. N - 1} : y < x
                     \/ (x = Bottom /\ {view[p][r] : r \in 0 .. N - 1} = {Bottom})]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED <<view, prop, estimate, crashed, sent, recv>>

Crash(p) ==
  /\ phase[p] \notin {"crashed", "done"}
  /\ crashed < F
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ crashed' = crashed + 1
  /\ UNCHANGED <<view, prop, estimate, decision, sent, recv>>

Next ==
  \/ \E p \in 0 .. N - 1 : BroadcastP1(p)
  \/ \E p \in 0 .. N - 1, m \in sent : RecvP1(p, m)
  \/ \E p \in 0 .. N - 1 : Prepare(p)
  \/ \E p \in 0 .. N - 1 : BroadcastP2(p)
  \/ \E p \in 0 .. N - 1, m \in sent : RecvP2(p, m)
  \/ \E p \in 0 .. N - 1 : Decide(p)
  \/ \E p \in 0 .. N - 1 : Choose(p)
  \/ \E p \in 0 .. N - 1 : PickChoice(p)
  \/ \E p \in 0 .. N - 1 : Crash(p)

\* Messages can be delivered in any order, so the model must be weakly fair
\* on every destination-action pair, not just on each action by itself.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in 0 .. N - 1 :
       /\ WF_vars(\E m \in sent : RecvP1(p, m))
       /\ WF_vars(\E m \in sent : RecvP2(p, m))
       /\ WF_vars(BroadcastP1(p))
       /\ WF_vars(Prepare(p))
       /\ WF_vars(BroadcastP2(p))
       /\ WF_vars(Decide(p))
       /\ WF_vars(PickChoice(p))

Validity ==
  \A p \in 0 .. N - 1 : decision[p] # Bottom => decision[p] \in Values

Agreement ==
  \A q1, q2 \in 0 .. N - 1 :
    (decision[q1] # Bottom /\ decision[q2] # Bottom) => decision[q1] = decision[q2]

Terminate == <>(\A p \in 0 .. N - 1 : phase[p] \in {"done", "crashed"})

C1 ==
  LET maxVal == CHOOSE m \in Values : \A v \in Values : v <= m
  IN Cardinality({p \in 0 .. N - 1 : prop[p] = maxVal}) >= F + 1

Conditional == C1 ~> Terminate

====