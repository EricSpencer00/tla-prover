---- MODULE cbc_max ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

\* ---------- Basic sets ----------
Proc == 1 .. N

PC == {"b1", "w1", "b2", "w2", "done", "crashed", "choose"}

Msg == [type   : {"phase1", "phase2"},
        val    : Values,
        sender : Proc,
        est    : Values \cup {Bottom}]

\* ---------- State variables ----------
VARIABLES pc, view, prop, est, dec, crashedCount, sent, rcv

vars == << pc, view, prop, est, dec, crashedCount, sent, rcv >>

\* ---------- Helper operators ----------
Max(S) ==
  IF S = {} THEN Bottom
  ELSE CHOOSE v \in S : \A w \in S : w <= v

ReceivedFrom(p, typ) ==
  { m.sender : m \in rcv[p] /\ m.type = typ }

ReceivedEstSet(p) ==
  { m.est : m \in rcv[p] /\ m.type = "phase2" }

EnoughPhase1(p) ==
  Cardinality(ReceivedFrom(p, "phase1")) >= N - T

EnoughPhase2(p) ==
  \E e \in Values :
    Cardinality({ m \in rcv[p] :
                  m.type = "phase2" /\ m.est = e }) >= N - T

AllPhase2(p) ==
  Cardinality(ReceivedFrom(p, "phase2")) = N

\* ---------- Initialization ----------
Init ==
  /\ pc = [p \in Proc |-> "b1"]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ prop \in [Proc -> Values]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ rcv = [p \in Proc |-> {}]

\* ---------- Actions ----------
BroadcastPhase1(p) ==
  /\ pc[p] = "b1"
  /\ pc' = [pc EXCEPT ![p] = "w1"]
  /\ sent' = sent \cup { [type |-> "phase1",
                         val  |-> prop[p],
                         sender|-> p,
                         est  |-> Bottom] }
  /\ UNCHANGED << view, prop, est, dec, crashedCount, rcv >>

ReceivePhase1(p, m) ==
  /\ m \in sent
  /\ m.type = "phase1"
  /\ pc[p] = "w1"
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

ComputeEst(p) ==
  /\ pc[p] = "w1"
  /\ EnoughPhase1(p)
  /\ LET vals == { view[p][q] : q \in Proc } \ {Bottom} IN
        TRUE
  /\ est' = [est EXCEPT ![p] = Max({ view[p][q] : q \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "b2"]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, rcv >>

BroadcastPhase2(p) ==
  /\ pc[p] = "b2"
  /\ pc' = [pc EXCEPT ![p] = "w2"]
  /\ sent' = sent \cup { [type |-> "phase2",
                         val  |-> prop[p],
                         sender|-> p,
                         est  |-> est[p]] }
  /\ UNCHANGED << view, prop, est, dec, crashedCount, rcv >>

ReceivePhase2(p, m) ==
  /\ m \in sent
  /\ m.type = "phase2"
  /\ pc[p] = "w2"
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ rcv' = [rcv EXCEPT ![p] = rcv[p] \cup {m}]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

Decide(p, e) ==
  /\ pc[p] = "w2"
  /\ e \in Values
  /\ Cardinality({ m \in rcv[p] : m.type = "phase2" /\ m.est = e }) >= N - T
  /\ dec' = [dec EXCEPT ![p] = e]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, rcv >>

MoveToChoose(p) ==
  /\ pc[p] = "w2"
  /\ AllPhase2(p)
  /\ \A e \in Values :
        Cardinality({ m \in rcv[p] : m.type = "phase2" /\ m.est = e }) < N - T
  /\ pc' = [pc EXCEPT ![p] = "choose"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, sent, rcv >>

ChooseAndDecide(p) ==
  /\ pc[p] = "choose"
  /\ LET vals == { view[p][q] : q \in Proc } \ {Bottom} IN
        vals # {}
  /\ let v == CHOOSE x \in vals : TRUE in
        TRUE
  /\ dec' = [dec EXCEPT ![p] = v]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << view, prop, est, crashedCount, sent, rcv >>

Crash(p) ==
  /\ pc[p] # "crashed"
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, rcv >>

Next ==
  \E p \in Proc :
    \/ BroadcastPhase1(p)
    \/ \E m \in Msg : ReceivePhase1(p, m)
    \/ ComputeEst(p)
    \/ BroadcastPhase2(p)
    \/ \E m \in Msg : ReceivePhase2(p, m)
    \/ \E e \in Values : Decide(p, e)
    \/ MoveToChoose(p)
    \/ ChooseAndDecide(p)
    \/ Crash(p)

\* ---------- Specification ----------
Spec == Init /\ [][Next]_vars

\* ---------- Type correctness ----------
TypeOK ==
  /\ pc \in [Proc -> PC]
  /\ view \in [Proc -> [Proc -> (Values \cup {Bottom})]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> (Values \cup {Bottom})]
  /\ dec \in [Proc -> (Values \cup {Bottom})]
  /\ crashedCount \in Nat
  /\ sent \subseteq Msg
  /\ rcv \in [Proc -> SUBSET Msg]

\* ---------- Safety properties ----------
Validity ==
  \A p \in Proc :
    dec[p] # Bottom => (\E q \in Proc : prop[q] = dec[p])

Agreement ==
  \A p, q \in Proc :
    /\ dec[p] # Bottom
    /\ dec[q] # Bottom
    => dec[p] = dec[q]

====