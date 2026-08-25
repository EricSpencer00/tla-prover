---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N, T, F, Values, Bottom

\* ----------------------------------------------------------------------
\* Type definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N

PhaseType == {"b1", "w1", "b2", "w2", "choosing", "done", "crashed"}

Message ==
  UNION {
    { [type |-> "p1",  value |-> v,    sender |-> s] :
        v \in Values, s \in Proc },
    { [type |-> "p2",  value |-> v,    est |-> e, sender |-> s] :
        v \in Values, e \in Values, s \in Proc }
  }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES phase, proposed, view, est, dec, sent, rcvd

vars == << phase, proposed, view, est, dec, sent, rcvd >>

\* ----------------------------------------------------------------------
\* Helper functions
\* ----------------------------------------------------------------------
\* Set of values that a process p has learned (non‑Bottom)
LearnedVals(p) == { view[p][q] : q \in Proc /\ view[p][q] # Bottom }

\* Maximum of a non‑empty set of values (Values are totally ordered)
MaxInSet(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : v >= w

\* Maximum value seen by p after phase 1
MaxInView(p) == MaxInSet(LearnedVals(p))

\* Number of processes that have crashed
CrashCount == Cardinality({ p \in Proc : phase[p] = "crashed" })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ phase = [p \in Proc |-> "b1"]
  /\ proposed = [p \in Proc |-> CHOOSE v \in Values : TRUE]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ sent = {}
  /\ rcvd = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
BroadcastPhase1(p) ==
  /\ phase[p] = "b1"
  /\ LET m == [type |-> "p1", value |-> proposed[p], sender |-> p] IN
        /\ sent' = sent \cup {m}
  /\ phase' = [phase EXCEPT ![p] = "w1"]
  /\ UNCHANGED << proposed, view, est, dec, rcvd >>

ReceivePhase1(p, m) ==
  /\ phase[p] = "w1"
  /\ m \in sent
  /\ m.type = "p1"
  /\ view' = [view EXCEPT ![p][m.sender] = m.value]
  /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
  /\ UNCHANGED << phase, proposed, est, dec, sent >>

ComputeEst(p) ==
  /\ phase[p] = "w1"
  /\ Cardinality({ q \in Proc : view[p][q] # Bottom }) >= N - T
  /\ est' = [est EXCEPT ![p] = MaxInView(p)]
  /\ phase' = [phase EXCEPT ![p] = "b2"]
  /\ UNCHANGED << proposed, view, dec, sent, rcvd >>

BroadcastPhase2(p) ==
  /\ phase[p] = "b2"
  /\ LET m == [type |-> "p2", value |-> proposed[p],
               est |-> est[p], sender |-> p] IN
        /\ sent' = sent \cup {m}
  /\ phase' = [phase EXCEPT ![p] = "w2"]
  /\ UNCHANGED << proposed, view, est, dec, rcvd >>

ReceivePhase2(p, m) ==
  /\ phase[p] = "w2"
  /\ m \in sent
  /\ m.type = "p2"
  /\ rcvd' = [rcvd EXCEPT ![p] = rcvd[p] \cup {m}]
  /\ UNCHANGED << phase, proposed, view, est, dec, sent >>

Decide(p, v) ==
  /\ phase[p] = "w2"
  /\ v \in Values
  /\ Cardinality({ m \in rcvd[p] : m.type = "p2" /\ m.est = v }) >= N - T
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED << proposed, view, est, sent, rcvd >>

MoveToChoosing(p) ==
  /\ phase[p] = "w2"
  /\ { m.sender : m \in rcvd[p] /\ m.type = "p2" } = Proc
  /\ \A v \in Values :
        Cardinality({ m \in rcvd[p] : m.type = "p2" /\ m.est = v }) < N - T
  /\ phase' = [phase EXCEPT ![p] = "choosing"]
  /\ UNCHANGED << proposed, view, est, dec, sent, rcvd >>

ChooseAndDecide(p) ==
  /\ phase[p] = "choosing"
  /\ LET v == MaxInView(p) IN
        /\ v # Bottom
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ phase' = [phase EXCEPT ![p] = "done"]
  /\ UNCHANGED << proposed, view, est, sent, rcvd >>

Crash(p) ==
  /\ phase[p] # "crashed"
  /\ CrashCount < F
  /\ phase' = [phase EXCEPT ![p] = "crashed"]
  /\ UNCHANGED << proposed, view, est, dec, sent, rcvd >>

Next ==
  \/ \E p \in Proc : BroadcastPhase1(p)
  \/ \E p \in Proc, m \in Message : ReceivePhase1(p, m)
  \/ \E p \in Proc : ComputeEst(p)
  \/ \E p \in Proc : BroadcastPhase2(p)
  \/ \E p \in Proc, m \in Message : ReceivePhase2(p, m)
  \/ \E p \in Proc, v \in Values : Decide(p, v)
  \/ \E p \in Proc : MoveToChoosing(p)
  \/ \E p \in Proc : ChooseAndDecide(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
  /\ phase \in [Proc -> PhaseType]
  /\ proposed \in [Proc -> Values]
  /\ view \in [Proc -> [Proc -> Values]]
  /\ est \in [Proc -> Values]
  /\ dec \in [Proc -> Values]
  /\ sent \subseteq Message
  /\ rcvd \in [Proc -> SUBSET Message]
  /\ Bottom \notin Values
  /\ N \in Nat
  /\ T \in Nat
  /\ F \in Nat
  /\ 2 * T < N
  /\ 0 <= F
  /\ F <= T
  /\ N > 0

\* ----------------------------------------------------------------------
\* Safety properties
\* ----------------------------------------------------------------------
Validity ==
  \A p \in Proc :
    dec[p] # Bottom =>
      \E q \in Proc : proposed[q] = dec[p]

Agreement ==
  \A p, q \in Proc :
    (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

====