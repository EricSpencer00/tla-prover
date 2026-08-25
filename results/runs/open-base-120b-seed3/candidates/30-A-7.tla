---- MODULE cbc_max ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F, Values, Bottom

VARIABLES pc, view, prop, est, dec, crashedCount, sent, recv

\* ----------------------------------------------------------------------
\* Basic sets
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"p1", "p2"},
            val  : Values,
            sender : Proc,
            est  : Values]   \* est is Bottom for phase‑1 messages

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
  /\ pc = [p \in Proc |-> "bcast1"]
  /\ prop \in [Proc -> Values]
  /\ view = [p \in Proc |-> [q \in Proc |-> Bottom]]
  /\ est = [p \in Proc |-> Bottom]
  /\ dec = [p \in Proc |-> Bottom]
  /\ crashedCount = 0
  /\ sent = {}
  /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Max(S) ==
  IF S = {} THEN Bottom
  ELSE LET m == CHOOSE x \in S : \A y \in S : y <= x IN m

CanComputeEst(p) ==
  /\ pc[p] = "wait1"
  /\ Cardinality({ s \in Proc : view[p][s] # Bottom }) >= N - T

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Send1(p) ==
  /\ p \in Proc
  /\ pc[p] = "bcast1"
  /\ sent' = sent \cup
        { [type |-> "p1",
           val  |-> prop[p],
           sender |-> p,
           est  |-> Bottom] }
  /\ pc' = [pc EXCEPT ![p] = "wait1"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

Receive1(p, m) ==
  /\ p \in Proc
  /\ pc[p] = "wait1"
  /\ m \in sent
  /\ m.type = "p1"
  /\ m.sender \in Proc
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ view' = [view EXCEPT ![p][m.sender] = m.val]
  /\ UNCHANGED << pc, prop, est, dec, crashedCount, sent >>

ComputeEst(p) ==
  /\ CanComputeEst(p)
  /\ est' = [est EXCEPT ![p] = Max({ view[p][s] : s \in Proc })]
  /\ pc' = [pc EXCEPT ![p] = "bcast2"]
  /\ UNCHANGED << view, prop, dec, crashedCount, sent, recv >>

Send2(p) ==
  /\ p \in Proc
  /\ pc[p] = "bcast2"
  /\ sent' = sent \cup
        { [type |-> "p2",
           val  |-> prop[p],
           sender |-> p,
           est  |-> est[p]] }
  /\ pc' = [pc EXCEPT ![p] = "wait2"]
  /\ UNCHANGED << view, prop, est, dec, crashedCount, recv >>

Receive2(p, m) ==
  /\ p \in Proc
  /\ pc[p] = "wait2"
  /\ m \in sent
  /\ m.type = "p2"
  /\ m.sender \in Proc
  /\ m \notin recv[p]
  /\ recv' = [recv EXCEPT ![p] = recv[p] \cup {m}]
  /\ UNCHANGED << pc, view, prop, est, dec, crashedCount, sent >>

Decide(p) ==
  /\ p \in Proc
  /\ pc[p] = "wait2"
  /\ \E v \in Values :
        /\ Cardinality({ m \in recv[p] :
                         m.type = "p2" /\ m.est = v }) >= N - T
        /\ dec' = [dec EXCEPT ![p] = v]
        /\ pc' = [pc EXCEPT ![p] = "done"]
        /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Choose(p) ==
  /\ p \in Proc
  /\ pc[p] = "wait2"
  /\ { m.sender : m \in recv[p] /\ m.type = "p2" } = Proc
  /\ \A v \in Values :
        Cardinality({ m \in recv[p] :
                       m.type = "p2" /\ m.est = v }) < N - T
  /\ LET cand == Max({ view[p][s] :
                         s \in Proc /\ view[p][s] # Bottom }) IN
        /\ cand # Bottom
        /\ dec' = [dec EXCEPT ![p] = cand]
        /\ pc' = [pc EXCEPT ![p] = "done"]
        /\ UNCHANGED << view, prop, est, crashedCount, sent, recv >>

Crash(p) ==
  /\ p \in Proc
  /\ pc[p] # "crashed"
  /\ crashedCount < F
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ crashedCount' = crashedCount + 1
  /\ UNCHANGED << view, prop, est, dec, sent, recv >>

Next ==
  \/ \E p \in Proc : Send1(p)
  \/ \E p \in Proc : \E m \in sent : Receive1(p, m)
  \/ \E p \in Proc : ComputeEst(p)
  \/ \E p \in Proc : Send2(p)
  \/ \E p \in Proc : \E m \in sent : Receive2(p, m)
  \/ \E p \in Proc : Decide(p)
  \/ \E p \in Proc : Choose(p)
  \/ \E p \in Proc : Crash(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< pc, view, prop, est, dec, crashedCount, sent, recv >>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"bcast1","wait1","bcast2","wait2","done","crashed","choose"}]
  /\ view \in [Proc -> [Proc -> Values \cup {Bottom}]]
  /\ prop \in [Proc -> Values]
  /\ est \in [Proc -> Values \cup {Bottom}]
  /\ dec \in [Proc -> Values \cup {Bottom}]
  /\ crashedCount \in Nat
  /\ sent \subseteq Message
  /\ recv \in [Proc -> SUBSET Message]

Validity ==
  \A p \in Proc : dec[p] # Bottom => dec[p] \in Values

Agreement ==
  \A p,q \in Proc :
     (dec[p] # Bottom /\ dec[q] # Bottom) => dec[p] = dec[q]

====