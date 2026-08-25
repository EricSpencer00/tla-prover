---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Derived sets and constants
\* ----------------------------------------------------------------------
Proc == 1..N

PC == {"b1",            \* broadcasting phase‑1
       "w1",            \* waiting for phase‑1 messages
       "b2",            \* broadcasting phase‑2
       "w2",            \* waiting for phase‑2 messages
       "choose",        \* deterministic choosing state
       "done",          \* finished with a decision
       "crashed"}       \* crashed process

Msg == [type : {"p1","p2"},
        sender : Proc,
        value : Values,
        est : Values \cup {Bottom}]   \* est = Bottom for p1 messages

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES pc,               \* [p \in Proc |-> PC]
          view,             \* [p \in Proc |-> [q \in Proc |-> Values \cup {Bottom}]]
          prop,             \* [p \in Proc |-> Values]
          est,              \* [p \in Proc |-> Values \cup {Bottom}]
          decision,         \* [p \in Proc |-> Values \cup {Bottom}]
          crashedCount,     \* Nat
          msgs,             \* SUBSET Msg
          rcv               \* [p \in Proc |-> SUBSET Msg]

vars == << pc, view, prop, est, decision, crashedCount, msgs, rcv >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsMax(v, S) == v \in S /\ \A w \in S : w <= v

Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : IsMax(v, S)

ReceivedFrom(p, phase) ==
  { m["sender"] : /\ m \in rcv[p] /\ m["type"] = phase }

CountEst(p, v) ==
  Cardinality({ m \in rcv[p] : /\ m["type"] = "p2" /\ m["est"] = v })

\* ----------------------------------------------------------------------
\* Type correctness
\* ----------------------------------------------------------------------
TypeOK ==
 /\ N \in Nat
 /\ T \in Nat
 /\ F \in Nat
 /\ 0 <= F /\ F <= T
 /\ 2 * T < N
 /\ Values \subseteq Nat
 /\ Bottom \notin Values
 /\ pc \in [Proc -> PC]
 /\ prop \in [Proc -> Values]
 /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
 /\ est \in [Proc -> (Values \cup {Bottom})]
 /\ decision \in [Proc -> (Values \cup {Bottom})]
 /\ crashedCount \in Nat
 /\ msgs \subseteq Msg
 /\ rcv \in [Proc -> SUBSET Msg]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
 /\ pc = [p \in Proc |-> "b1"]
 /\ prop \in [Proc -> Values]   \* each process chooses a value
 /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
 /\ est = [p \in Proc |-> Bottom]
 /\ decision = [p \in Proc |-> Bottom]
 /\ crashedCount = 0
 /\ msgs = {}
 /\ rcv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
 /\ pc[p] = "b1"
 /\ msgs' = msgs \cup { [type |-> "p1",
                        sender |-> p,
                        value |-> prop[p],
                        est |-> Bottom] }
 /\ pc' = [pc EXCEPT ![p] = "w1"]
 /\ UNCHANGED << view, prop, est, decision, crashedCount, rcv >>

ReceivePhase1(p, m) ==
 /\ pc[p] = "w1"
 /\ m \in msgs
 /\ m["type"] = "p1"
 /\ view' = [view EXCEPT ![p][m["sender"]] = m["value"]]
 /\ rcv'  = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
 /\ UNCHANGED << pc, prop, est, decision, crashedCount, msgs >>

ComputeEst(p) ==
 /\ pc[p] = "w1"
 /\ Cardinality(ReceivedFrom(p, "p1")) >= N - T
 /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
 /\ pc' = [pc EXCEPT ![p] = "b2"]
 /\ UNCHANGED << view, prop, decision, crashedCount, msgs, rcv >>

BroadcastPhase2(p) ==
 /\ pc[p] = "b2"
 /\ msgs' = msgs \cup { [type |-> "p2",
                        sender |-> p,
                        value |-> prop[p],
                        est |-> est[p]] }
 /\ pc' = [pc EXCEPT ![p] = "w2"]
 /\ UNCHANGED << view, prop, est, decision, crashedCount, rcv >>

ReceivePhase2(p, m) ==
 /\ pc[p] = "w2"
 /\ m \in msgs
 /\ m["type"] = "p2"
 /\ view' = [view EXCEPT ![p][m["sender"]] = m["value"]]
 /\ rcv'  = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
 /\ UNCHANGED << pc, prop, est, decision, crashedCount, msgs >>

DecideFromEst(p, v) ==
 /\ pc[p] = "w2"
 /\ CountEst(p, v) >= N - T
 /\ decision' = [decision EXCEPT ![p] = v]
 /\ pc' = [pc EXCEPT ![p] = "done"]
 /\ UNCHANGED << view, prop, est, crashedCount, msgs, rcv >>

MoveToChoose(p) ==
 /\ pc[p] = "w2"
 /\ Cardinality(ReceivedFrom(p, "p2")) = N    \* all senders heard
 /\ \A v \in Values : CountEst(p, v) < N - T
 /\ pc' = [pc EXCEPT ![p] = "choose"]
 /\ UNCHANGED << view, prop, est, decision, crashedCount, msgs, rcv >>

Choose(p) ==
 /\ pc[p] = "choose"
 /\ \E v \in Values :
        /\ v \in { view[p][q] : q \in Proc }
        /\ decision' = [decision EXCEPT ![p] = v]
 /\ pc' = [pc EXCEPT ![p] = "done"]
 /\ UNCHANGED << view, prop, est, crashedCount, msgs, rcv >>

Crash(p) ==
 /\ pc[p] /= "crashed"
 /\ crashedCount < F
 /\ pc' = [pc EXCEPT ![p] = "crashed"]
 /\ crashedCount' = crashedCount + 1
 /\ UNCHANGED << view, prop, est, decision, msgs, rcv >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
 \/ \E p \in Proc : BroadcastPhase1(p)
 \/ \E p \in Proc, m \in msgs : ReceivePhase1(p, m)
 \/ \E p \in Proc : ComputeEst(p)
 \/ \E p \in Proc : BroadcastPhase2(p)
 \/ \E p \in Proc, m \in msgs : ReceivePhase2(p, m)
 \/ \E p \in Proc, v \in Values : DecideFromEst(p, v)
 \/ \E p \in Proc : MoveToChoose(p)
 \/ \E p \in Proc : Choose(p)
 \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Validity ==
 \A p \in Proc :
   decision[p] # Bottom => decision[p] \in Values

Agreement ==
 \A p, q \in Proc :
   /\ decision[p] # Bottom
   /\ decision[q] # Bottom
   => decision[p] = decision[q]

\* ----------------------------------------------------------------------
\* End of module
\* ----------------------------------------------------------------------
====